#include <stdlib.h>
#include <stdio.h>
#include <parlib.h>
#include <unistd.h>
#include <signal.h>
#include <nixip.h>

/*
 *  well known IP addresses
 */
uint8_t IPv4bcast[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff
};
uint8_t IPv4allsys[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xe0, 0, 0, 0x01
};
uint8_t IPv4allrouter[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xe0, 0, 0, 0x02
};
uint8_t IPallbits[IPaddrlen] = {
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff
};
uint8_t IPnoaddr[IPaddrlen];

/*
 *  prefix of all v4 addresses
 */
uint8_t v4prefix[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0, 0, 0, 0
};

int
isv4(uint8_t *ip)
{
	return memcmp(ip, v4prefix, IPv4off) == 0;
}

/*
 *  the following routines are unrolled with no memset's to speed
 *  up the usual case
 */
void
v4tov6(uint8_t *v6, uint8_t *v4)
{
	v6[0] = 0;
	v6[1] = 0;
	v6[2] = 0;
	v6[3] = 0;
	v6[4] = 0;
	v6[5] = 0;
	v6[6] = 0;
	v6[7] = 0;
	v6[8] = 0;
	v6[9] = 0;
	v6[10] = 0xff;
	v6[11] = 0xff;
	v6[12] = v4[0];
	v6[13] = v4[1];
	v6[14] = v4[2];
	v6[15] = v4[3];
}

int
v6tov4(uint8_t *v4, uint8_t *v6)
{
	if(v6[0] == 0
	&& v6[1] == 0
	&& v6[2] == 0
	&& v6[3] == 0
	&& v6[4] == 0
	&& v6[5] == 0
	&& v6[6] == 0
	&& v6[7] == 0
	&& v6[8] == 0
	&& v6[9] == 0
	&& v6[10] == 0xff
	&& v6[11] == 0xff)
	{
		v4[0] = v6[12];
		v4[1] = v6[13];
		v4[2] = v6[14];
		v4[3] = v6[15];
		return 0;
	} else {
		memset(v4, 0, 4);
		if(memcmp(v6, IPnoaddr, IPaddrlen) == 0)
			return 0;
		return -1;
	}
}
