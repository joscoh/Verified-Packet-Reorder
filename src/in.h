//This is in netinet/in.h in the Linux C standard library, but we need to give some (trivial) specs

//For our purposes, we don't care about endianness; only that everything is done in host byte order on the machine. So we define uninterpreted functions htons and ntohl and assume that the C functions implement these:

#ifndef IN_H
#define IN_H

#include <stdint.h>

//@ fixpoint int ntohl(int netlong);

//@ fixpoint int ntohs(int netshort);

//@ fixpoint int htons(int hostshort);

// This is not necessarily true universally, but it is certainly true in x86, ARM, etc. For this case, we need this lemma for the verification 
// due to what we believe is a mistake (see tcp_reorder.c).

/*@ 
lemma void htons_ntohs(int x);
requires 0 <= x && x <= 65535;
ensures htons(x) == ntohs(x);
@*/

uint16_t htons(uint16_t hostshort);
//@requires 0 <= hostshort && hostshort <= UINT16_MAX;
//@ ensures result == htons(hostshort);

uint32_t ntohl(uint32_t netlong);
//@requires 0 <= netlong && netlong <= UINT32_MAX;
//@ensures result == ntohl(netlong);

uint16_t ntohs(uint16_t netshort);
//@requires 0 <= netshort && netshort <= UINT16_MAX;
//@ensures result == ntohs(netshort);

#endif /* IN_H */