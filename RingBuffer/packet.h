#ifndef _PACKET_H_INCLUDED_
#define _PACKET_H_INCLUDED_

//#include "vigor.h"

struct packet {
  int port;
};

/*@
  inductive packet = packet(int);

  predicate packetp(struct packet* p; packet pkt) =
     struct_packet_padding(p) &*&
     p->port |-> ?port &*&
     pkt == packet(port);
     
  lemma void packet_layout_assumption();
  requires true;
  ensures sizeof(struct packet) < 1024;
@*/

static bool receive_packet(struct packet* dst)
//@ requires true;
//@ ensures true;
{
  return true;
  /*if (SYMBOLIC("received")) {
    dst->port = SYMBOLIC("port");
    return 1;
  }
  return 0;*/
}

static bool can_send_packet()
//@ requires true;
//@ ensures result == true;
{
  return true;
  //if (SYMBOLIC("can_send_packet")) return 1;
  //return 0;
}

static void send_packet(struct packet* src)
//@ requires packet_port(src, ?i) &*& i != 9;
//@ ensures packet_port(src, i);
{
////@ open packetp(src, packet(i));
  assert(src->port != 9);
}

#endif//_PACKET_H_INCLUDED_
