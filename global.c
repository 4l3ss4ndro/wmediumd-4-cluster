/*
 *	wmediumd, wireless medium simulator for mac80211_hwsim kernel module
 *	Copyright (c) 2011 cozybit Inc.
 *
 *	Author:	Javier Lopez	<jlopex@cozybit.com>
 *		Javier Cardona	<javier@cozybit.com>
 *
 *	This program is free software; you can redistribute it and/or
 *	modify it under the terms of the GNU General Public License
 *	as published by the Free Software Foundation; either version 2
 *	of the License, or (at your option) any later version.
 *
 *	This program is distributed in the hope that it will be useful,
 *	but WITHOUT ANY WARRANTY; without even the implied warranty of
 *	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *	GNU General Public License for more details.
 *
 *	You should have received a copy of the GNU General Public License
 *	along with this program; if not, write to the Free Software
 *	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 *	02110-1301, USA.
 */

#include <stdint.h>
#include <getopt.h>
#include <signal.h>
#include <event.h>
#include <math.h>
#include <sys/timerfd.h>
#include <errno.h>
#include <limits.h>
#include <unistd.h>
#include <pthread.h>
// #include <linux/netlink.h>
#include "wmediumd.h"
#include "ieee80211.h"
#include "config.h"
#include "wserver.h"
#include "wmediumd_dynamic.h"
#include "wserver_messages.h"
#include <unistd.h>
#include <string.h>	//strlen
#include <sys/socket.h>	//socket
#include <arpa/inet.h>	//inet_addr
#include <netinet/in.h>

int socket_to_global = 0;
struct wmediumd *ctx_to_pass;
int sockfd_udp;                        
struct sockaddr_in addr_udp;

static inline int div_round(int a, int b)
{
	return (a + b - 1) / b;
}

static inline int pkt_duration(struct wmediumd *ctx, int len, int rate)
{
	/* preamble + signal + t_sym * n_sym, rate in 100 kbps */
	return 16 + 4 + 4 * div_round((16 + 8 * len + 6) * 10, 4 * rate);
}

int w_logf(struct wmediumd *ctx, u8 level, const char *format, ...)
{
	va_list(args);
	va_start(args, format);
	if (ctx->log_lvl >= level) {
		return vprintf(format, args);
	}
	return -1;
}

int w_flogf(struct wmediumd *ctx, u8 level, FILE *stream, const char *format, ...)
{
	va_list(args);
	va_start(args, format);
	if (ctx->log_lvl >= level) {
		return vfprintf(stream, format, args);
	}
	return -1;
}

static void wqueue_init(struct wqueue *wqueue, int cw_min, int cw_max)
{
	INIT_LIST_HEAD(&wqueue->frames);
	wqueue->cw_min = cw_min;
	wqueue->cw_max = cw_max;
}

void station_init_queues(struct station *station)
{
	wqueue_init(&station->queues[IEEE80211_AC_BK], 15, 1023);
	wqueue_init(&station->queues[IEEE80211_AC_BE], 15, 1023);
	wqueue_init(&station->queues[IEEE80211_AC_VI], 7, 15);
	wqueue_init(&station->queues[IEEE80211_AC_VO], 3, 7);
}

bool timespec_before(struct timespec *t1, struct timespec *t2)
{
	return t1->tv_sec < t2->tv_sec ||
	       (t1->tv_sec == t2->tv_sec && t1->tv_nsec < t2->tv_nsec);
}

void timespec_add_usec(struct timespec *t, int usec)
{
	printf("In timespec_add_usec\n");
	t->tv_nsec += usec * 1000;
	if (t->tv_nsec >= 1000000000) {
		t->tv_sec++;
		t->tv_nsec -= 1000000000;
	}
}

// a - b = c
static int timespec_sub(struct timespec *a, struct timespec *b,
			struct timespec *c)
{
	c->tv_sec = a->tv_sec - b->tv_sec;

	if (a->tv_nsec < b->tv_nsec) {
		c->tv_sec--;
		c->tv_nsec = 1000000000 + a->tv_nsec - b->tv_nsec;
	} else {
		c->tv_nsec = a->tv_nsec - b->tv_nsec;
	}

	return 0;
}

void rearm_timer(struct wmediumd *ctx)
{
	struct timespec min_expires;
	struct itimerspec expires;
	struct station *station;
	struct frame *frame;
	int i;
	printf("In rearm_timer\n");
	bool set_min_expires = false;

	/*
	 * Iterate over all the interfaces to find the next frame that
	 * will be delivered, and set the timerfd accordingly.
	 */
	list_for_each_entry(station, &ctx->stations, list) {
		for (i = 0; i < IEEE80211_NUM_ACS; i++) {
			frame = list_first_entry_or_null(&station->queues[i].frames,
							 struct frame, list);

			if (frame && (!set_min_expires ||
				      timespec_before(&frame->expires,
						      &min_expires))) {
				set_min_expires = true;
				min_expires = frame->expires;
			}
		}
	}

	if (set_min_expires) {
		memset(&expires, 0, sizeof(expires));
		expires.it_value = min_expires;
		timerfd_settime(ctx->timerfd, TFD_TIMER_ABSTIME, &expires,
				NULL);
	}
}

static inline bool frame_has_a4(struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;

	return (hdr->frame_control[1] & (FCTL_TODS | FCTL_FROMDS)) ==
		(FCTL_TODS | FCTL_FROMDS);
}

static inline bool frame_is_mgmt(struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;

	return (hdr->frame_control[0] & FCTL_FTYPE) == FTYPE_MGMT;
}

static inline bool frame_is_data(struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;

	return (hdr->frame_control[0] & FCTL_FTYPE) == FTYPE_DATA;
}

static inline bool frame_is_data_qos(struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;

	return (hdr->frame_control[0] & (FCTL_FTYPE | STYPE_QOS_DATA)) ==
		(FTYPE_DATA | STYPE_QOS_DATA);
}

static inline u8 *frame_get_qos_ctl(struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;

	if (frame_has_a4(frame))
		return (u8 *)hdr + 30;
	else
		return (u8 *)hdr + 24;
}

static enum ieee80211_ac_number frame_select_queue_80211(struct frame *frame)
{
	u8 *p;
	int priority;

	if (!frame_is_data(frame))
		return IEEE80211_AC_VO;

	if (!frame_is_data_qos(frame))
		return IEEE80211_AC_BE;

	p = frame_get_qos_ctl(frame);
	priority = *p & QOS_CTL_TAG1D_MASK;

	return ieee802_1d_to_ac[priority];
}

static double dBm_to_milliwatt(int decibel_intf)
{
#define INTF_LIMIT (31)
	int intf_diff = NOISE_LEVEL - decibel_intf;

	if (intf_diff >= INTF_LIMIT)
		return 0.001;

	if (intf_diff <= -INTF_LIMIT)
		return 1000.0;

	return pow(10.0, -intf_diff / 10.0);
}

static double milliwatt_to_dBm(double value)
{
	return 10.0 * log10(value);
}

static int set_interference_duration(struct wmediumd *ctx, int src_idx,
				     int duration, int signal)
{
	fprintf(stdout, "In set_interference_duration function\n");
	int i, medium_id;

	if (!ctx->intf)
		return 0;

	if (signal >= CCA_THRESHOLD)
		return 0;

    medium_id = ctx->sta_array[src_idx]->medium_id;
	for (i = 0; i < ctx->num_stas; i++) {
        if (medium_id != ctx->sta_array[i]->medium_id)
            continue;
		ctx->intf[ctx->num_stas * src_idx + i].duration += duration;
		// use only latest value
		ctx->intf[ctx->num_stas * src_idx + i].signal = signal;
	}

	return 1;
}

static int get_signal_offset_by_interference(struct wmediumd *ctx, int src_idx,
					     int dst_idx)
{
	fprintf(stdout, "In get_signal_offset_by_interference function\n");
    int i, medium_id;
	double intf_power;

	if (!ctx->intf)
		return 0;

	intf_power = 0.0;
    medium_id = ctx->sta_array[dst_idx]->medium_id;
	for (i = 0; i < ctx->num_stas; i++) {
		if (i == src_idx || i == dst_idx)
			continue;
        if (medium_id != ctx->sta_array[i]->medium_id)
            continue;
		if (drand48() < ctx->intf[i * ctx->num_stas + dst_idx].prob_col)
			intf_power += dBm_to_milliwatt(
				ctx->intf[i * ctx->num_stas + dst_idx].signal);
	}

	if (intf_power <= 1.0)
		return 0;

	return (int)(milliwatt_to_dBm(intf_power) + 0.5);
}

bool is_multicast_ether_addr(const u8 *addr)
{
	return 0x01 & addr[0];
}

static struct station *get_station_by_addr(struct wmediumd *ctx, u8 *addr)
{
	struct station *station;

	list_for_each_entry(station, &ctx->stations, list) {
		if (memcmp(station->addr, addr, ETH_ALEN) == 0)
			return station;
	}
	return NULL;
}

void detect_mediums(struct wmediumd *ctx, struct station *src, struct station *dest) {
    int medium_id;
    fprintf(stdout, "In detect_mediums function\n");
    if (!ctx->enable_medium_detection){
        return;
    }
    if(src->isap& !dest->isap){
        // AP-STA Connection
        medium_id = -src->index-1;
    }else if((!src->isap)& dest->isap){
        // STA-AP Connection
        medium_id = -dest->index-1;
    }else{
        // AP-AP Connection
        // STA-STA Connection
        // TODO: Detect adhoc and mesh groups
        return;
    }
    if (medium_id!=src->medium_id){
        w_logf(ctx, LOG_DEBUG, "Setting medium id of " MAC_FMT "(%d|%s) to %d.\n",
               MAC_ARGS(src->addr), src->index, src->isap ? "AP" : "Sta",
               medium_id);
        src-> medium_id = medium_id;
    }
    if(medium_id!=dest->medium_id){
        w_logf(ctx, LOG_DEBUG, "Setting medium id of " MAC_FMT "(%d|%s) to %d.\n",
               MAC_ARGS(dest->addr), dest->index, dest->isap ? "AP" : "Sta",
               medium_id);
        dest-> medium_id = medium_id;
    }
}
void queue_frame(struct wmediumd *ctx, struct station *station,
		 struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *)frame->data;
	u8 *dest = hdr->addr1;
	struct timespec now, target;
	struct wqueue *queue;
	struct frame *tail;
	struct station *tmpsta, *deststa;
	int send_time;
	int cw;
	double error_prob;
	bool is_acked = false;
	bool noack = false;
	int i, j;
	int rate_idx;
	int ac;

	/* TODO configure phy parameters */
	int slot_time = 9;
	int sifs = 16;
	int difs = 2 * slot_time + sifs;

	int retries = 0;

	clock_gettime(CLOCK_MONOTONIC, &now);

	int ack_time_usec = pkt_duration(ctx, 14, index_to_rate(0, frame->freq)) +
			sifs;
	fprintf(stdout, "In queue_frame function\n");
	/*
	 * To determine a frame's expiration time, we compute the
	 * number of retries we might have to make due to radio conditions
	 * or contention, and add backoff time accordingly.  To that, we
	 * add the expiration time of the previous frame in the queue.
	 */

	ac = frame_select_queue_80211(frame);
	queue = &station->queues[ac];

	/* try to "send" this frame at each of the rates in the rateset */
	send_time = 0;
	cw = queue->cw_min;

	int snr = SNR_DEFAULT;

	if (is_multicast_ether_addr(dest)) {
		deststa = NULL;
		fprintf(stdout, "multicast TRUE\n");
	} else {
		deststa = get_station_by_addr(ctx, dest);
		if (deststa) {
            w_logf(ctx, LOG_DEBUG, "Packet from " MAC_FMT "(%d|%s) to " MAC_FMT "(%d|%s)\n",
                   MAC_ARGS(station->addr), station->index, station->isap ? "AP" : "Sta",
                   MAC_ARGS(deststa->addr), deststa->index, deststa->isap ? "AP" : "Sta");
            fprintf(stdout, "Packet from " MAC_FMT "(%d|%s) to " MAC_FMT "(%d|%s)\n",
                   MAC_ARGS(station->addr), station->index, station->isap ? "AP" : "Sta",
                   MAC_ARGS(deststa->addr), deststa->index, deststa->isap ? "AP" : "Sta");
            detect_mediums(ctx,station,deststa);
			snr = ctx->get_link_snr(ctx, station, deststa) -
				get_signal_offset_by_interference(ctx,
					station->index, deststa->index);
			snr += ctx->get_fading_signal(ctx);
		}
	}
	frame->signal = snr + NOISE_LEVEL;

	noack = frame_is_mgmt(frame) || is_multicast_ether_addr(dest);
	double choice = -3.14;

	if (use_fixed_random_value(ctx))
		choice = drand48();

	for (i = 0; i < frame->tx_rates_count && !is_acked; i++) {

		rate_idx = frame->tx_rates[i].idx;
		fprintf(stdout, "Rate: %d\n", rate_idx);

		/* no more rates in MRR */
		if (rate_idx < 0)
			break;

		error_prob = ctx->get_error_prob(ctx, snr, rate_idx,
						 frame->freq, frame->data_len,
						 station, deststa);
		for (j = 0; j < frame->tx_rates[i].count; j++) {
			send_time += difs + pkt_duration(ctx, frame->data_len,
				index_to_rate(rate_idx, frame->freq));

			retries++;

			/* skip ack/backoff/retries for noack frames */
			if (noack) {
				is_acked = true;
				break;
			}

			/* TODO TXOPs */

			/* backoff */
			if (j > 0) {
				send_time += (cw * slot_time) / 2;
				cw = (cw << 1) + 1;
				if (cw > queue->cw_max)
					cw = queue->cw_max;
			}
			if (!use_fixed_random_value(ctx))
				choice = drand48();
			if (choice > error_prob) {
				is_acked = true;
				break;
			}
			send_time += ack_time_usec;
		}
	}
	if (is_acked) {
		frame->tx_rates[i-1].count = j + 1;
		for (; i < frame->tx_rates_count; i++) {
			frame->tx_rates[i].idx = -1;
			frame->tx_rates[i].count = -1;
		}
		frame->flags |= HWSIM_TX_STAT_ACK;
	}

	/*
	 * delivery time starts after any equal or higher prio frame
	 * (or now, if none).
	 */
	target = now;
    w_logf(ctx, LOG_DEBUG, "Sta " MAC_FMT " medium is #%d\n", MAC_ARGS(station->addr), station->medium_id);
    list_for_each_entry(tmpsta, &ctx->stations, list) {
        if (station->medium_id == tmpsta->medium_id) {
            w_logf(ctx, LOG_DEBUG, "Sta " MAC_FMT " medium is also #%d\n", MAC_ARGS(tmpsta->addr),
                   tmpsta->medium_id);
            for (i = 0; i <= ac; i++) {
                tail = list_last_entry_or_null(&tmpsta->queues[i].frames,
                                               struct frame, list);
                if (tail && timespec_before(&target, &tail->expires))
                    target = tail->expires;
            }
        } else {
            w_logf(ctx, LOG_DEBUG, "Sta " MAC_FMT " medium is not #%d, it is #%d\n", MAC_ARGS(tmpsta->addr),
                   station->medium_id, tmpsta->medium_id);
        }
    }
	
	timespec_add_usec(&target, send_time);
	frame->duration = send_time;
	frame->expires = target;
	list_add_tail(&frame->list, &queue->frames);
	rearm_timer(ctx);
}

int send_to_broadcast(int sockfd_udp, int data_len, int rate_idx, int signal,
			  int freq, u8 *hwaddr, u8 *data)
{
	mystruct_tobroadcast broad_mex;
	
	broad_mex.data_len_tobroadcast = data_len;
	broad_mex.rate_idx_tobroadcast = rate_idx;
	broad_mex.signal_tobroadcast = signal;
	broad_mex.freq_tobroadcast = freq;
	memcpy(broad_mex.hwaddr, hwaddr, ETH_ALEN);
	memcpy(broad_mex.data_tobroadcast, data, data_len);
	//printf("Dest Station for broadcast " MAC_FMT "\n", MAC_ARGS(station->hwaddr));
	
	/* Broadcast broad_mex in datagram to clients */
	if (sendto(sockfd_udp, (mystruct_tobroadcast*)&broad_mex, sizeof(mystruct_tobroadcast), 0, (struct sockaddr *)&addr_udp, sizeof(addr_udp)) != sizeof(mystruct_tobroadcast)){
	    fprintf(stderr, "broadcast sendto error");
	    exit(1);
	}
	else
		printf("HWSIM_CMD_FRAME broadcast sent\n");
		
	return 0;
}

int send_to_local(int sock, struct frame *frame)
{
	mystruct_frame server_reply;
	mystruct_frame* frame_tosend;
	frame_tosend = &server_reply;
	
	server_reply.cookie_tosend = frame->cookie;
	server_reply.flags_tosend = frame->flags;
	server_reply.tx_rates_count_tosend = frame->tx_rates_count;
	memcpy(server_reply.tx_rates_tosend, frame->tx_rates, sizeof(frame->tx_rates));
	server_reply.signal_tosend = frame->signal;
	//sleep(2);
	//Send the message back to client
	send(sock, frame_tosend, sizeof(mystruct_frame), 0);
	fprintf(stdout, "Tx info sent\n");
		
	return 0;
}

void deliver_frame(struct wmediumd *ctx, struct frame *frame)
{
	struct ieee80211_hdr *hdr = (void *) frame->data;
	struct station *station;
	u8 *dest = hdr->addr1;
	u8 *src = frame->sender->addr;
	int sock = socket_to_global;
	
	int rate_idx;
	fprintf(stdout, "In deliver_frame function\n");
	if (frame->flags & HWSIM_TX_STAT_ACK) {
		/* rx the frame on the dest interface */
		list_for_each_entry(station, &ctx->stations, list) {
			if (memcmp(src, station->addr, ETH_ALEN) == 0)
				continue;

			if (is_multicast_ether_addr(dest)) {
				int snr, signall;
				double error_prob;
				/*
				 * we may or may not receive this based on
				 * reverse link from sender -- check for
				 * each receiver.
				 */
				snr = ctx->get_link_snr(ctx, frame->sender,
							station);
				snr += ctx->get_fading_signal(ctx);
				signall = snr + NOISE_LEVEL;
				if (signall < CCA_THRESHOLD)
					continue;

				if (set_interference_duration(ctx,
					frame->sender->index, frame->duration,
					signall))
					continue;

				snr -= get_signal_offset_by_interference(ctx,
					frame->sender->index, station->index);
				rate_idx = frame->tx_rates[0].idx;
				error_prob = ctx->get_error_prob(ctx,
					(double)snr, rate_idx, frame->freq,
					frame->data_len, frame->sender,
					station);

				if (drand48() <= error_prob) {
					w_logf(ctx, LOG_INFO, "Dropped mcast from "
						   MAC_FMT " to " MAC_FMT " at receiver\n",
						   MAC_ARGS(src), MAC_ARGS(station->addr));
					continue;
				}
				
				send_to_broadcast(sockfd_udp, frame->data_len, rate_idx, signall,
			  			  frame->freq, station->hwaddr, frame->data);
				
			} else if (memcmp(dest, station->addr, ETH_ALEN) == 0) {
				if (set_interference_duration(ctx,
					frame->sender->index, frame->duration,
					frame->signal))
					continue;
				rate_idx = frame->tx_rates[0].idx;
				
				send_to_broadcast(sockfd_udp, frame->data_len, rate_idx, frame->signal,
			  			  frame->freq, station->hwaddr, frame->data);
  			}
		}
	} else
		set_interference_duration(ctx, frame->sender->index,
					  frame->duration, frame->signal);

	send_to_local(sock, frame);

	free(frame);
}

void deliver_expired_frames_queue(struct wmediumd *ctx,
				  struct list_head *queue,
				  struct timespec *now)
{
	struct frame *frame, *tmp;
	fprintf(stdout, "In deliver_expired_frames_queue function\n");
	list_for_each_entry_safe(frame, tmp, queue, list) {
		if (timespec_before(&frame->expires, now)) {
			list_del(&frame->list);
			deliver_frame(ctx, frame);
		} else {
			break;
		}
	}
}

void deliver_expired_frames(struct wmediumd *ctx)
{
	struct timespec now, _diff;
	struct station *station;
	struct list_head *l;
    int i, j, duration;
    int sta1_medium_id;
    fprintf(stdout, "In deliver_expired_frames function\n");

	clock_gettime(CLOCK_MONOTONIC, &now);
	list_for_each_entry(station, &ctx->stations, list) {
		int q_ct[IEEE80211_NUM_ACS] = {};
		for (i = 0; i < IEEE80211_NUM_ACS; i++) {
			list_for_each(l, &station->queues[i].frames) {
				q_ct[i]++;
			}
		}
		w_logf(ctx, LOG_DEBUG, "[" TIME_FMT "] Station " MAC_FMT
					   " BK %d BE %d VI %d VO %d\n",
			   TIME_ARGS(&now), MAC_ARGS(station->addr),
			   q_ct[IEEE80211_AC_BK], q_ct[IEEE80211_AC_BE],
			   q_ct[IEEE80211_AC_VI], q_ct[IEEE80211_AC_VO]);

		for (i = 0; i < IEEE80211_NUM_ACS; i++)
			deliver_expired_frames_queue(ctx, &station->queues[i].frames, &now);
	}
	w_logf(ctx, LOG_DEBUG, "\n\n");

	if (!ctx->intf)
		return;

	timespec_sub(&now, &ctx->intf_updated, &_diff);
	duration = (_diff.tv_sec * 1000000) + (_diff.tv_nsec / 1000);
	if (duration < 10000) // calc per 10 msec
		return;

	// update interference
	for (i = 0; i < ctx->num_stas; i++){
        sta1_medium_id = ctx->sta_array[i]->medium_id;
        for (j = 0; j < ctx->num_stas; j++) {
            if (i == j)
                continue;
            if (sta1_medium_id != ctx->sta_array[j]->medium_id)
                continue;
            // probability is used for next calc
            ctx->intf[i * ctx->num_stas + j].prob_col =
                    ctx->intf[i * ctx->num_stas + j].duration /
                    (double)duration;
            ctx->intf[i * ctx->num_stas + j].duration = 0;
        }
    }

	clock_gettime(CLOCK_MONOTONIC, &ctx->intf_updated);
}

static
int nl_err_cb(struct sockaddr_nl *nla, struct nlmsgerr *nlerr, void *arg)
{
	struct genlmsghdr *gnlh = nlmsg_data(&nlerr->msg);
	struct wmediumd *ctx = arg;

	w_flogf(ctx, LOG_DEBUG, stderr, "nl: cmd %d, seq %d: %s\n", gnlh->cmd,
			nlerr->msg.nlmsg_seq, strerror(abs(nlerr->error)));

	return NL_SKIP;
}

/*
 * Handle events from the kernel.  Process CMD_FRAME events and queue them
 * for later delivery with the scheduler.
 */
static int process_messages_cb(void *arg, mystruct_nlmsg torecv_t)
{
	struct wmediumd *ctx = arg;
	struct station *sender;
	struct frame *frame;
	
	fprintf(stdout, "In process_messages function\n");
	
	if (1) {
		pthread_rwlock_rdlock(&snr_lock);
		fprintf(stdout, "HWSIM_CMD_FRAME received\n");
		if (1) {
			//fprintf(stdout, "Attributes got\n");
			u8 *hwaddr = (u8 *)malloc(sizeof(u8)*ETH_ALEN);
			//for(int j = 0; j < ETH_ALEN; j++)	
			//	hwaddr[j] = torecv_t.hwaddr_t[j];
			memcpy(hwaddr, torecv_t.hwaddr_t, ETH_ALEN);
			unsigned int data_len = torecv_t.data_len_t;
			unsigned int flags = torecv_t.flags_t;
			unsigned int tx_rates_len = torecv_t.tx_rates_len_t;
			struct hwsim_tx_rate *tx_rates = (struct hwsim_tx_rate *)malloc(sizeof(struct hwsim_tx_rate)*IEEE80211_TX_MAX_RATES);
			//for(int j = 0; j < IEEE80211_TX_MAX_RATES; j++)
			//	tx_rates[j] = torecv_t.tx_rates_t[j];
			memcpy(tx_rates, torecv_t.tx_rates_t, sizeof(IEEE80211_TX_MAX_RATES));
			u64 cookie =  torecv_t.cookie_t;
			u32 freq = torecv_t.freq_t;
			u8 *src = (u8 *)malloc(sizeof(u8)*ETH_ALEN);
			//for(int j = 0; j < ETH_ALEN; j++)
			//	src[j] = torecv_t.src_t[j];
			memcpy(src, torecv_t.src_t, ETH_ALEN);
			u8 *data = (u8 *)malloc(sizeof(u8)*10000);
			memcpy(data, torecv_t.data_t, sizeof(torecv_t.data_t));
			
			printf("Socket data received\n");
			
			//printf("Sender sta " MAC_FMT "\n", MAC_ARGS(src));

			sender = get_station_by_addr(ctx, src);
			if (!sender) {
				printf("Unable to find sender station " MAC_FMT "\n", MAC_ARGS(src));
				w_flogf(ctx, LOG_ERR, stderr, "Unable to find sender station " MAC_FMT "\n", MAC_ARGS(src));
				goto out;
			}
			else
				printf("Sender sta found\n");
			memcpy(sender->hwaddr, hwaddr, ETH_ALEN);

			frame = malloc(sizeof(*frame) + data_len);
			if (!frame)
				goto out;

			memcpy(frame->data, data, data_len);
			frame->data_len = data_len;
			frame->flags = flags;
			frame->cookie = cookie;
			frame->freq = freq;
			frame->sender = sender;
			sender->freq = freq;
			frame->tx_rates_count =
				tx_rates_len / sizeof(struct hwsim_tx_rate);
			memcpy(frame->tx_rates, tx_rates,
			       min(tx_rates_len, sizeof(frame->tx_rates)));
			fprintf(stdout, "Frame queued\n");
			queue_frame(ctx, sender, frame);
		}

out:
	pthread_rwlock_unlock(&snr_lock);
	return 0;
	
	}	
	return 0;
}

/*
 * Register with the kernel to start receiving new frames.
 */
int send_register_msg(struct wmediumd *ctx)
{
	struct nl_sock *sock = ctx->sock;
	struct nl_msg *msg;
	int ret;
	fprintf(stdout, "Registering HWSIM_CMD_REGISTER...\n");
	msg = nlmsg_alloc();
	if (!msg) {
		w_logf(ctx, LOG_ERR, "Error allocating new message MSG!\n");
		return -1;
	}

	if (genlmsg_put(msg, NL_AUTO_PID, NL_AUTO_SEQ, ctx->family_id,
			0, NLM_F_REQUEST, HWSIM_CMD_REGISTER,
			VERSION_NR) == NULL) {
		w_logf(ctx, LOG_ERR, "%s: genlmsg_put failed\n", __func__);
		fprintf(stdout, "Failing registering\n");
		ret = -1;
		goto out;
	}

	ret = nl_send_auto_complete(sock, msg);
	if (ret < 0) {
		w_logf(ctx, LOG_ERR, "%s: nl_send_auto failed\n", __func__);
		fprintf(stdout, "Failing registering\n");
		ret = -1;
		goto out;
	}
	ret = 0;

out:
	nlmsg_free(msg);
	return ret;
}

static void sock_event_cb(int fd, short what, void *data)
{
	struct wmediumd *ctx = data;
	nl_recvmsgs_default(ctx->sock);
}

/*
 * Setup netlink socket and callbacks.
 */
static int init_netlink(struct wmediumd *ctx)
{
	struct nl_sock *sock;
	int ret;

	ctx->cb = nl_cb_alloc(NL_CB_CUSTOM);
	if (!ctx->cb) {
		w_logf(ctx, LOG_ERR, "Error allocating netlink callbacks\n");
		return -1;
	}

	sock = nl_socket_alloc_cb(ctx->cb);
	if (!sock) {
		w_logf(ctx, LOG_ERR, "Error allocating netlink socket\n");
		return -1;
	}

	ctx->sock = sock;

	ret = genl_connect(sock);
	if (ret < 0) {
		w_logf(ctx, LOG_ERR, "Error connecting netlink socket ret=%d\n", ret);
		return -1;
	}

	ctx->family_id = genl_ctrl_resolve(sock, "MAC80211_HWSIM");
	if (ctx->family_id < 0) {
		w_logf(ctx, LOG_ERR, "Family MAC80211_HWSIM not registered\n");
		return -1;
	}

	nl_cb_err(ctx->cb, NL_CB_CUSTOM, nl_err_cb, ctx);

	return 0;
}

/*
 *	Print the CLI help
 */
void print_help(int exval)
{
	printf("wmediumd v%s - a wireless medium simulator\n", VERSION_STR);
	printf("wmediumd [-h] [-V] [-s] [-l LOG_LVL] [-x FILE] -c FILE\n\n");

	printf("  -h              print this help and exit\n");
	printf("  -V              print version and exit\n\n");

	printf("  -l LOG_LVL      set the logging level\n");
	printf("                  LOG_LVL: RFC 5424 severity, values 0 - 7\n");
	printf("                  >= 3: errors are logged\n");
	printf("                  >= 5: startup msgs are logged\n");
	printf("                  >= 6: dropped packets are logged (default)\n");
	printf("                  == 7: all packets will be logged\n");
	printf("  -c FILE         set input config file\n");
	printf("  -x FILE         set input PER file\n");
	printf("  -s              start the server on a socket\n");
	printf("  -d              use the dynamic complex mode\n");
	printf("                  (server only with matrices for each connection)\n");

	exit(exval);
}

static void timer_cb(int fd, short what, void *data)
{
	struct wmediumd *ctx = data;
	uint64_t u;
	
	fprintf(stdout, "In timer_cb function\n");

	pthread_rwlock_rdlock(&snr_lock);
	read(fd, &u, sizeof(u));
	ctx->move_stations(ctx);
	deliver_expired_frames(ctx);
	rearm_timer(ctx);
	pthread_rwlock_unlock(&snr_lock);
}

void *connection_handler(void *socket_desc)
{
	fprintf(stdout, "Inside connection handler\n");
	//Get the socket descriptor
	int sock = *(int*)socket_desc;
	int read_size;
	struct wmediumd *ctx = ctx_to_pass;
	mystruct_nlmsg *client_message;
	mystruct_nlmsg torecv;
    	client_message = &torecv;
	
	socket_to_global = sock;
	
	//Receive a message from client
	fprintf(stdout, "Waiting for messages from client\n");
	while(1)
	{
		while( (read_size = recv(sock, client_message, sizeof(mystruct_nlmsg), 0) > 0 ))
		{
			fprintf(stdout, "TCP message received\n");
			process_messages_cb(ctx, torecv);
		}
	}
	
	if(read_size == 0)
	{
		puts("Client disconnected");
		fflush(stdout);
	}
	else if(read_size == -1)
	{
		perror("TCP recv failed");
	}	
	//Free the socket pointer
	free(socket_desc);
	
	return NULL;
}

int main(int argc, char *argv[])
{
	struct event ev_cmd;
	struct event ev_timer;
	struct wmediumd ctx;
	char *config_file = NULL;
	char *per_file = NULL;
	int opt;
	 
   	int server_tcp, new_socket;
	struct sockaddr_in address;
	int opt_tcp = 1;
	int addrlen = sizeof(address);
	int *new_sock;
	char *ip_udp = "192.168.1.255";
	int port_udp = 8080;
	int yes = 1;

	fprintf(stdout, "In main\n");

	setvbuf(stdout, NULL, _IOLBF, BUFSIZ);

	if (argc == 1) {
		fprintf(stderr, "This program needs arguments....\n\n");
		print_help(EXIT_FAILURE);
	}

	ctx.log_lvl = 7;
	unsigned long int parse_log_lvl;
	char* parse_end_token;
	bool start_server = false;
	bool full_dynamic = false;

	while ((opt = getopt(argc, argv, "hVc:l:x:sd")) != -1) {
		switch (opt) {
		case 'h':
			print_help(EXIT_SUCCESS);
			break;
		case 'V':
			printf("wmediumd v%s - a wireless medium simulator "
			       "for mac80211_hwsim\n", VERSION_STR);
			exit(EXIT_SUCCESS);
			break;
		case 'c':
			config_file = optarg;
			break;
		case 'x':
			printf("Input packet error rate file: %s\n", optarg);
			per_file = optarg;
			break;
		case ':':
			printf("wmediumd: Error - Option `%c' "
			       "needs a value\n\n", optopt);
			print_help(EXIT_FAILURE);
			break;
		case 'l':
			parse_log_lvl = strtoul(optarg, &parse_end_token, 10);
			if ((parse_log_lvl == ULONG_MAX && errno == ERANGE) ||
			     optarg == parse_end_token || parse_log_lvl > 7) {
				printf("wmediumd: Error - Invalid RFC 5424 severity level: "
							   "%s\n\n", optarg);
				print_help(EXIT_FAILURE);
			}
			ctx.log_lvl = parse_log_lvl;
			break;
		case 'd':
			full_dynamic = true;
			break;
		case 's':
			start_server = true;
			break;
		case '?':
			printf("wmediumd: Error - No such option: "
			       "`%c'\n\n", optopt);
			print_help(EXIT_FAILURE);
			break;
		}

	}

	if (optind < argc)
		print_help(EXIT_FAILURE);

	if (full_dynamic) {
		if (config_file) {
			printf("%s: cannot use dynamic complex mode with config file\n", argv[0]);
			print_help(EXIT_FAILURE);
		}

		if (!start_server) {
			printf("%s: dynamic complex mode requires the server option\n", argv[0]);
			print_help(EXIT_FAILURE);
		}

		w_logf(&ctx, LOG_NOTICE, "Using dynamic complex mode instead of config file\n");
	} else {
		if (!config_file) {
			printf("%s: config file must be supplied\n", argv[0]);
			print_help(EXIT_FAILURE);
		}

		w_logf(&ctx, LOG_NOTICE, "Input configuration file: %s\n", config_file);
	}
	INIT_LIST_HEAD(&ctx.stations);
	if (load_config(&ctx, config_file, per_file, full_dynamic))
		return EXIT_FAILURE;
	
	/* init libevent */
	event_init();

	/* init netlink */
	if (init_netlink(&ctx) < 0)
		return EXIT_FAILURE;

	event_set(&ev_cmd, nl_socket_get_fd(ctx.sock), EV_READ | EV_PERSIST,
		  sock_event_cb, &ctx);
	event_add(&ev_cmd, NULL);

	/* setup timers */
	ctx.timerfd = timerfd_create(CLOCK_MONOTONIC, 0);
	clock_gettime(CLOCK_MONOTONIC, &ctx.intf_updated);
	clock_gettime(CLOCK_MONOTONIC, &ctx.next_move);
	ctx.next_move.tv_sec += MOVE_INTERVAL;
	event_set(&ev_timer, ctx.timerfd, EV_READ | EV_PERSIST, timer_cb, &ctx);
	event_add(&ev_timer, NULL);

	/* register for new frames */
	if (send_register_msg(&ctx) == 0) {
		w_logf(&ctx, LOG_NOTICE, "REGISTER SENT!\n");
	}

	if (start_server == true)
		start_wserver(&ctx);
		
	// Creating TCP socket file descriptor
	if ((server_tcp = socket(AF_INET, SOCK_STREAM, 0))
		== 0) {
		perror("socket failed");
		exit(EXIT_FAILURE);
	}

	// Forcefully attaching socket to the port 8090
	if (setsockopt(server_tcp, SOL_SOCKET,
				SO_REUSEADDR | SO_REUSEPORT, &opt_tcp,
				sizeof(opt_tcp))) {
		perror("setsockopt");
		exit(EXIT_FAILURE);
	}
	address.sin_family = AF_INET;
	address.sin_addr.s_addr = INADDR_ANY;//inet_addr(ip_tcp);
	address.sin_port = htons(8090);

	// Forcefully attaching socket to the port 8090
	if (bind(server_tcp, (struct sockaddr*)&address,
			sizeof(address))
		< 0) {
		perror("bind failed");
		exit(EXIT_FAILURE);
	}
	if (listen(server_tcp, 3) < 0) {
		perror("listen");
		exit(EXIT_FAILURE);
	}
	
	ctx_to_pass = &ctx;
	
	//Accept and incoming connection
	fprintf(stdout, "Waiting for incoming TCP connections...\n");
	
	new_socket = accept(server_tcp, (struct sockaddr*)&address,
				(socklen_t*)&addrlen);
	
	if (new_socket < 0)
	{
		perror("TCP accept failed");
		return 1;
	}
	else
		fprintf(stdout, "TCP connection accepted\n");
	
	pthread_t sniffer_thread;
	new_sock = malloc(1);
	*new_sock = new_socket;
	fprintf(stdout, "Creating thread for TCP messages\n");
	
	sleep(5);
	
	if( pthread_create( &sniffer_thread , NULL ,  connection_handler , (void*) new_sock) < 0)
		{
			fprintf(stdout, "Could not create thread\n");
			perror("could not create thread");
			return 1;
		}
	
	//UDP broadcast socket
	sockfd_udp = socket(AF_INET, SOCK_DGRAM, 0);

	int ret = setsockopt(sockfd_udp, SOL_SOCKET, SO_BROADCAST, (char*)&yes, sizeof(yes));
	if (ret == -1) {
	perror("setsockopt error");
	return 0;
	}
	int opt_reuse = 1;
 	setsockopt(sockfd_udp, SOL_SOCKET, SO_REUSEPORT, &opt_reuse, sizeof(opt_reuse));
  

	memset(&addr_udp, '\0', sizeof(addr_udp));
	addr_udp.sin_family = AF_INET;
	addr_udp.sin_port = htons(port_udp);
	addr_udp.sin_addr.s_addr = inet_addr(ip_udp);
	
	/* enter libevent main loop */
	event_dispatch();
	if (start_server == true)
		stop_wserver();
	
	free(ctx.sock);
	free(ctx.cb);
	free(ctx.intf);
	free(ctx.per_matrix);
	pthread_join( sniffer_thread , NULL);
	close(new_socket);
	shutdown(server_tcp, SHUT_RDWR);
	
	return EXIT_SUCCESS;
}
