#include "packet.h"
#include "ring.h"

#define RING_CAPACITY 512

/*@
  fixpoint bool packet_constraints_fp(packet p) {
    switch(p) { case packet(port): return port != 9; }
  }
  @*/
  
/*@
  predicate loop_invariant(struct ring* rp) =
    ringp(rp, packet_constraints_fp, _, RING_CAPACITY);
  @*/
 

int main(int argc, char** argv)
//@ requires true;
//@ ensures true;
{
  struct packet p;
  //@ close packet_property(packet_constraints_fp);
  struct ring *r = ring_create(RING_CAPACITY);
  if (!r) return 1;
  //@ close loop_invariant(r);
  while(1)
  //@ invariant loop_invariant(r) &*& packet_port(&p, ?i) &*& struct_packet_padding(&p);
  {
    //@open loop_invariant(r);
    if (!ring_full(r))
      if (receive_packet(&p) && p.port != 9)
        ring_push_back(r, &p);
    if (!ring_empty(r) && can_send_packet()) {
      ring_pop_front(r, &p);
      send_packet(&p);
    }
    //@close loop_invariant(r);
  }
  //@ assert false; //not reachable
  return 0;
}
