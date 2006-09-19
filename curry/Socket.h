/*
 * $Id: Socket.h 1903 2006-04-22 18:49:09Z wlux $
 *
 * Copyright (c) 2006, Wolfgang Lux
 *
 * See ../LICENSE for the full license
 *
 * Foreign function definitions for the Socket library
 */

#include "curry.h"
#include <sys/types.h>
#include <sys/time.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

/* compatibility */
/* NB use a pre-processor definition just in case configure got it wrong */
#ifndef HAVE_SOCKLEN_T
# define socklen_t int
#endif

/* address families */
#define prim_AF_INET()		AF_INET

/* socket domains */
#define prim_SOCK_STREAM()	SOCK_STREAM

/* bind wrapper */
static inline int
prim_bind(int s, int port)
{
    struct sockaddr_in addr;

    /* set up the address structure */
    addr.sin_family	 = AF_INET;
    addr.sin_port	 = htons(port);
    addr.sin_addr.s_addr = INADDR_ANY;
    memset(addr.sin_zero, 0, sizeof(addr.sin_zero));

    /* bind the socket */
    return bind(s, (struct sockaddr *)&addr, sizeof(addr));
}

/* determine port number of a socket */
static inline int
prim_getPort(int s)
{
    socklen_t	       len;
    struct sockaddr_in addr;

    /* get port from socket */
    len = sizeof(addr);
    if ( getsockname(s, (struct sockaddr *)&addr, &len) < 0 )
        return -1;
    return ntohs(addr.sin_port);
}

/* determine peer of a connection */
static inline char *
prim_getPeer(int s)
{
    socklen_t	       len;
    struct sockaddr_in addr;
    struct hostent     *hp;

    /* get peer address from socket */
    len = sizeof(addr);
    if ( getpeername(s, (struct sockaddr *)&addr, &len) < 0 )
	return 0;

    /* determine host name for peer if possible */
    hp = gethostbyaddr((char *)&addr.sin_addr, sizeof(addr.sin_addr), AF_INET);
    return hp ? hp->h_name : inet_ntoa(addr.sin_addr);
}

/* connect wrapper */
static inline int
prim_connect(int s, struct hostent *hostent, int port)
{
    struct sockaddr_in addr;

    /* set up the address structure */
    addr.sin_family	 = AF_INET;
    addr.sin_port	 = htons(port);
    addr.sin_addr.s_addr = *(unsigned long *)hostent->h_addr_list[0];
    memset(addr.sin_zero, 0, sizeof(addr.sin_zero));

    /* connect the socket */
    return connect(s, (struct sockaddr *)&addr, sizeof(struct sockaddr_in));
}

/* simple select wrapper */
static inline int
prim_waitForInput(int s, int to)
{
    fd_set	   rd;
    struct timeval tv;

    FD_ZERO(&rd);
    FD_SET(s, &rd);
    tv.tv_sec  = to / 1000;
    tv.tv_usec = (to % 1000) * 1000;
    return select(s+1, &rd, 0, 0, &tv);
}
