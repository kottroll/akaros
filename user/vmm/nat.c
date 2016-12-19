/* Copyright (c) 2016 Google Inc
 * Barret Rhoden <brho@cs.berkeley.edu>
 * See LICENSE for details.
 *
 * Network address translation for VM guests.
 *
 * TODO:
 * - We're working with the IOVs that the guest gave us through virtio.  If we
 *   care, that whole thing is susceptible to time-of-check attacks.  The guest
 *   could be modifying the IOV that we're working on, so we need to not care
 *   too much about that.
 * - Consider having the kernel proto bypass overwrite the src address enforcing
 *   the proto port.  We don't care about the proto payload.  We might care
 *   about IP and proto headers.  o/w, the user could fake traffic for other
 *   ports - basically they can craft whatever packet they want.
 * - Have an option for controlling whether or not we snoop on I/O.  Probably
 *   can inject from the same FD.
 * - Currently planning on using FD taps, and not threads, to watch all the host
 *   FDs.  The final reason for this is to avoid copies.  The concurrency with
 *   the guest is based on the number of IOVs they give us - not the number of
 *   host conversations open.  We could listen on 1000 convs, each with their
 *   own read buffer, but we'd then have to copy the entire packet into the IOVs
 *   the guest gave us.
 *
 * - Be careful about the length of the packet vs the length of the read/write
 *   done by the syscalls.  The retval of the read is how much data there is,
 *   including padding.  The actual packet headers say how much is usable.
 *
 * - Think about xsums.  We're changing the TCP ports, which means we'll need to
 *   adjust the xsum.  There is probably an easy way to adjust it without
 *   xsumming the whole iov/packet.  Same goes for IP header xsum.  And
 *   generating xsums for synthetic packets.
 *
 * - IPv6 support
 */

#include <vmm/nat.h>
#include <parlib/iovec.h>
#include <iplib/iplib.h>
#include <parlib/ros_debug.h>
#include <parlib/uthread.h>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/queue.h>

/* For qemu-style networking:
 * 		guest = 10.0.2.15, mask = 255.255.255.0, router = 10.0.2.2.
 * For real-addr networking:
 * 		guest = host_v4, mask = host mask, router = host's route
 * We won't actually route real-addr routes to the host's route directly.  If we
 * ever get an IP addr of 'router', that'll be redirected to the host's local IP
 * stack (127.0.0.1). */
uint8_t host_v4_addr[IPv4addrlen];
uint8_t loopback_v4_addr[IPv4addrlen];
uint8_t guest_v4_addr[IPv4addrlen];
uint8_t guest_v4_mask[IPv4addrlen];
uint8_t guest_v4_route[IPv4addrlen];
uint8_t guest_v4_dns[IPv4addrlen];

/* We'll use this in all our eth headers with the guest. */
uint8_t host_fake_eth_addr[] = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05};

int snoop_fd;

/* We map between host port and guest port for a given protcol.  We don't care
 * about confirming IP addresses or anything - we just swap ports. */
struct ip_nat_map {
	uint16_t					guest_port;
	uint16_t					host_port;
	uint8_t						protocol;
	int							host_data_fd;
	// XXX timeout info
};

/* Injection */
struct buf_pkt {
	STAILQ_ENTRY(buf_pkt)		next;
	uint8_t						*buf;
	size_t						sz;
};
STAILQ_HEAD(buf_pkt_stailq, buf_pkt);
struct buf_pkt_stailq inject_pkts = STAILQ_HEAD_INITIALIZER(inject_pkts);
uth_mutex_t inject_mtx;
uth_cond_var_t inject_cv;


static void hexdump_packet(struct iovec *iov, int iovcnt);
static void inject_buf_pkt(struct buf_pkt *bpkt);

static void snoop_on_virtio(void)
{
	int ret;
	int srvfd;
	int pipefd[2];
	char buf[MAX_PATH_LEN];

	ret = pipe(pipefd);
	assert(!ret);
	snoop_fd = pipefd[0];
	ret = snprintf(buf, sizeof(buf), "#srv/%s-%d", "snoop", getpid());
	srvfd = open(buf, O_RDWR | O_EXCL | O_CREAT | O_REMCLO, 0444);
	assert(srvfd >= 0);
	ret = snprintf(buf, sizeof(buf), "%d", pipefd[1]);
	ret = write(srvfd, buf, ret);
}

static void determine_ip_addrs(void)
{
// XXX QEMU style.  use iplib.h and maybe some new helpers for real-addr style
	host_v4_addr[0] = 10;
	host_v4_addr[1] = 0;
	host_v4_addr[2] = 2;
	host_v4_addr[3] = 2;

	loopback_v4_addr[0] = 127;
	loopback_v4_addr[1] = 0;
	loopback_v4_addr[2] = 0;
	loopback_v4_addr[3] = 1;

	guest_v4_addr[0] = 10;
	guest_v4_addr[1] = 0;
	guest_v4_addr[2] = 2;
	guest_v4_addr[3] = 15;

	guest_v4_mask[0] = 255;
	guest_v4_mask[1] = 255;
	guest_v4_mask[2] = 255;
	guest_v4_mask[3] = 0;

	guest_v4_route[0] = 10;
	guest_v4_route[1] = 0;
	guest_v4_route[2] = 2;
	guest_v4_route[3] = 2;

	guest_v4_dns[0] = 10;
	guest_v4_dns[1] = 0;
	guest_v4_dns[2] = 2;
	guest_v4_dns[3] = 2;
}

void vmm_nat_init(void)
{
	determine_ip_addrs();
	inject_mtx = uth_mutex_alloc();
	inject_cv = uth_cond_var_alloc();

	/* TODO: have an option for this from the main VMM */
	snoop_on_virtio();
}

static int handle_eth_tx(struct iovec *iov, int iovcnt)
{
	fprintf(stderr, "ETHERNET!!!!!!!!!!!!!!!!!!!!!!!\n\n\n");
	hexdump_packet(iov, iovcnt);
	return 0;
}

// XXX nasty len
#define DHCP_OPT_LEN 34
#define DHCP_RSP_LEN (236 + DHCP_OPT_LEN)

// XXX needs restructuring, prob from DHCP down, not eth up
static void fake_dhcp_response(struct iovec *iov, int iovcnt)
{
	struct buf_pkt *bpkt;
	uint8_t *p, *xsum_addr;
	uint8_t *req;
	size_t req_sz;

	bpkt = malloc(sizeof(struct buf_pkt));
	assert(bpkt);
	bpkt->sz = ETH_HDR_LEN + IPV4HDR_LEN + UDP_HDR_LEN + DHCP_RSP_LEN;
	bpkt->buf = malloc(bpkt->sz);
	assert(bpkt->buf);
	memset(bpkt->buf, 0, bpkt->sz);

	/* Easier to work with as a straight-up buffer */
	req_sz = iov_get_len(iov, iovcnt);
	req = malloc(req_sz);
	assert(req);
	iov_linearize(iov, iovcnt, req, req_sz);

	p = bpkt->buf;

	memcpy(p, host_fake_eth_addr, ETH_ADDR_LEN);
	p += ETH_ADDR_LEN;
	memcpy(p, req + ETH_ADDR_LEN, ETH_ADDR_LEN);
	p += ETH_ADDR_LEN;
	hnputs(p, ETH_TYPE_IPV4);
	p += 2;

	*p = 0x45;		/* version, etc */
	p += 2;
	hnputs(p, bpkt->sz - ETH_HDR_LEN);	/* Total len */
	p += 2;
	p += 4;
	*p = 255; 		/* TTL */
	p += 1;
	*p = IP_UDPPROTO;
	p += 1;
	xsum_addr = p;
	p += 2;
	memcpy(p, guest_v4_route, IPv4addrlen);
	p += IPv4addrlen;
	// XXX this is for an offer, not an ack...
	for (int i = 0; i < IPv4addrlen; i++)
		*p++ = 255;
	/* IP header xsum */
	hnputs(xsum_addr, ptclbsum(bpkt->buf + ETH_HDR_LEN, IPV4HDR_LEN));
	
	/* UDP */
	hnputs(p, 67);
	p += 2;
	hnputs(p, 68);
	p += 2;
	hnputs(p, bpkt->sz - ETH_HDR_LEN - IPV4HDR_LEN);	/* UDP + payload len */
	p += 2;
	xsum_addr = p;
	p += 2;
	/* For v4, we don't need to do the xsum */
	hnputs(xsum_addr, 0);

	/* DHCP */
	*p++ = 0x02;	/* response */
	*p++ = 0x01;	/* ethernet */
	*p++ = ETH_ADDR_LEN;
	*p++ = 0x00;	/* hops */

	/* TODO: copies XID; assumes the inbound packet had standard headers */
	memcpy(p, req + ETH_HDR_LEN + IPV4HDR_LEN + UDP_HDR_LEN + 4, 4);
	p += 4;
	p += 8;			/* secs, flags, CIADDR */
	memcpy(p, guest_v4_addr, IPv4addrlen);
	p += IPv4addrlen;
	memcpy(p, guest_v4_route, IPv4addrlen);
	p += IPv4addrlen;
	memcpy(p, guest_v4_route, IPv4addrlen);
	p += IPv4addrlen;

	memcpy(p, req + ETH_ADDR_LEN, ETH_ADDR_LEN);
	p += 16;	/* CHaddr has 16 bytes, we only use 6 */
	memcpy(p, "host", 5);
	p += 64;
	p += 128;

	/* DHCP options */
	*p++ = 99;		/* magic cookie */
	*p++ = 130;
	*p++ = 83;
	*p++ = 99;

	/* Extra len = 4 + 3 + 6 * addrs + 2 + hostname + 1 */ // 34
	
	/* DHCP Message Type */
	*p++ = 53;
	*p++ = 1;
	*p++ = 2;	// XXX DHCPOFFER.  will need something else for ACK

	/* Subnet Mask */
	*p++ = 1;
	*p++ = 4;
	memcpy(p, guest_v4_mask, IPv4addrlen);
	p += IPv4addrlen;

	/* Router */
	*p++ = 3;
	*p++ = 4;
	memcpy(p, guest_v4_route, IPv4addrlen);
	p += IPv4addrlen;

	/* DNS */
	*p++ = 6;
	*p++ = 4;
	memcpy(p, guest_v4_dns, IPv4addrlen);
	p += IPv4addrlen;

	/* Hostname */
	*p++ = 12;
	*p++ = 6;	// XXX this and servername, 6 == sizeof "guest"
	memcpy(p, "guest", 6);
	p += 6;

	/* End of opts */
	*p++ = 255;

	inject_buf_pkt(bpkt);
	

// XXX 
// 		linux tcpdump complained about xsum, looks like at the IP layer.
// 			might be tcpdump.  check snoopy
//
// 		the guest's hostname is fucked
// 			should be fixed now
//
	free(req);
//        ether(s=1c:b7:2c:ee:52:69 d=ff:ff:ff:ff:ff:ff pr=0800 ln=342)
//        ip(s=0.0.0.0 d=255.255.255.255 id=0000 frag=0000 ttl= 64 pr=17 ln=328 hl=20)
//        udp(s=68 d=67 ck=52ab ln= 308)
//        bootp(t=Req ht=1 hl=6 hp=0 xid=e10c5958 sec=29 fl=0000 ca=0.0.0.0 ya=0.0.0.0 sa=0.0.0.0 ga=0.0.0.0 cha=1c:b7:2c:ee:52:69 magic=63825363)
//        dhcp(t=Discover clientid=011cb72cee5269 maxmsg=576  requested=(1 3 6 12 15 28 42) vendorclass=udhcp 1.24.2)
//

// 095296 ms 
//         ether(s=1c:b7:2c:ee:52:69 d=b8:ae:ed:76:f7:54 pr=0800 ln=590)
//         ip(s=100.107.10.100 d=100.107.10.67 id=c3cd frag=0000 ttl=255 pr=17 ln=576 hl=20)
//         udp(s=68 d=67 ck=30eb ln= 556)
//         bootp(t=Req ht=1 hl=6 hp=0 xid=ce98069 sec=0 fl=0000 ca=100.107.10.100 ya=0.0.0.0 sa=0.0.0.0 ga=0.0.0.0 cha=1c:b7:2c:ee:52:69 magic=63825363)
//         dhcp(t=Request clientid=011cb72cee5269 lease=1800 vendorclass=plan9_amd64  requested=(1 3 6 12 15 42))
//
// 095339 ms 
//         ether(s=b8:ae:ed:76:f7:54 d=1c:b7:2c:ee:52:69 pr=0800 ln=397)
//         ip(s=100.107.10.67 d=100.107.10.100 id=8312 frag=0000 ttl=255 pr=17 ln=383 hl=20)
//         udp(s=67 d=68 ck=5d60 ln= 363)
//         bootp(t=Rep ht=1 hl=6 hp=0 xid=ce98069 sec=0 fl=0000 ca=100.107.10.100 ya=100.107.10.100 sa=100.107.10.67 ga=0.0.0.0 cha=1c:b7:2c:ee:52:69 magic=63825363 s)
//         dhcp(t=Ack lease=1800 serverid=( 100.107.10.67) mask=( 255.255.255.192) router=( 100.107.10.126) hostname=madras.akaros.cam.lab.google.com dnssrv=( 100.107)
// 1
}


static int handle_ipv4_tx(struct iovec *iov, int iovcnt)
{
	uint16_t guest_src_port;
	uint8_t version, protocol;
	size_t ip_off = ETH_HDR_LEN;
	size_t proto_hdr_off;

	if (!iov_has_bytes(iov, iovcnt, IP_VER4 + ip_off)) {
		fprintf(stderr, "Short IPv4 header, dropping!\n");
		return -1;
	}
	protocol = iov_get_byte(iov, iovcnt, ip_off + 9);
	proto_hdr_off = (iov_get_byte(iov, iovcnt, ip_off + 0) & 0x0f) * 4 + ip_off;

	// XXX better infrastructure for this
	if (protocol == IP_UDPPROTO) {
		if (iov_get_be16(iov, iovcnt, proto_hdr_off + 2) == 67) {
			fake_dhcp_response(iov, iovcnt);
			return 0;
		}

	}
	// some things are faked by us (DHCP, inject response, done).  similarly for
	// arp
	//
	// some things are rerouted to us, from us.  if they are sending to
	// ROUTER_IP.  (send to 127.0.0.1 REMOTE_PORT, from 127.0.0.1 HOST_PORT)
	//
	// all others are routed outbound.  send to REMOTE ADDR: REMOTE PORT from
	// HOST_IP: HOST_PORT

}

static int handle_ipv6_tx(struct iovec *iov, int iovcnt)
{
	return -1;
}

/* virtio-net calls this when the guest transmits a packet */
int transmit_packet(struct iovec *iov, int iovcnt)
{
	uint16_t ether_type;
	int ret;

	writev(snoop_fd, iov, iovcnt);
	if (!iov_has_bytes(iov, iovcnt, ETH_HDR_LEN)) {
		fprintf(stderr, "Short ethernet frame from the guest, dropping!\n");
		return -1;
	}
	ether_type = iov_get_be16(iov, iovcnt, 12);

	switch (ether_type) {
	case ETH_TYPE_ARP:
		ret = handle_eth_tx(iov, iovcnt);
		break;
	case ETH_TYPE_IPV4:
		ret = handle_ipv4_tx(iov, iovcnt);
		break;
	case ETH_TYPE_IPV6:
		ret = handle_ipv6_tx(iov, iovcnt);
		break;
	default:
		fprintf(stderr, "Unknown ethertype 0x%x, dropping!\n", ether_type);
		return -1;
	};
	return ret;
}

/* XXX: maybe an event queue or something to make it easier for the other side
 * to wait.  (they want to wait on CVs AND evqs.  can we model CVs as evqs?). */
static void inject_buf_pkt(struct buf_pkt *bpkt)
{
	uth_mutex_lock(inject_mtx);
	STAILQ_INSERT_TAIL(&inject_pkts, bpkt, next);
	uth_mutex_unlock(inject_mtx);
	uth_cond_var_broadcast(inject_cv);
}

// XXX somewhere else, we need someone reading on all of the open convs
// 		could be the one virtio thread, or we could have N threads
// 		might be easier to tap them all
// 		o/w the virtio thread will need to block on a chan that all the others
// 		can push down
// 			linked list of iov[] arrays

// XXX this is the guest receiving a packet.  the virtio thread is usually
// blocked in here, i think
int receive_packet(struct iovec *iov, int iovcnt)
{
	// XXX this needs to be threadsafe - might have multiple receiver threads in
	// the future

	// look for injected packets, need to wake and shit.  can do this with an
	// evq in the future, maybe

	// XXX this only sleeps on inject, not the convs
	// 		could have an evq kick the CV.  not ideal, but it'll work
	//
	// 		alternatives:
	// 			have CV be an mbox type (so we can blockon all)
	// 			use a BCQ or something to inject (usermode or not) to an evq
	// 			btw, can we implement uth_block_on with a global CV/lock?
	struct buf_pkt *bpkt;

	uth_mutex_lock(inject_mtx);
	while (STAILQ_EMPTY(&inject_pkts))
		uth_cond_var_wait(inject_cv, inject_mtx);
	bpkt = STAILQ_FIRST(&inject_pkts);
	STAILQ_REMOVE_HEAD(&inject_pkts, next);
	uth_mutex_unlock(inject_mtx);

	// XXX assertions for these bufs?
	memcpy(iov->iov_base, bpkt->buf, MIN(bpkt->sz, iov->iov_len));
	int ret = bpkt->sz;
	free(bpkt->buf);
	free(bpkt);

	// XXX i think they want to block
	//sleep(9999999999);


	/* once we know what we want, we can write it out */
	writev(snoop_fd, iov, iovcnt);
	return ret;

}

static void hexdump_packet(struct iovec *iov, int iovcnt)
{
	uint8_t *buf;
	size_t len;

	len = iov_get_len(iov, iovcnt);
	buf = malloc(len);
	iov_linearize(iov, iovcnt, buf, len);
	fprintf(stderr, "Dumping packet:\n------------\n");
	hexdump(stderr, buf, len);
	fflush(stderr);
	free(buf);
}
