/*
 *
 * Copyright (c) 2009-2012, 2016 The University of Waikato, Hamilton,
 * New Zealand.
 * All rights reserved.
 *
 * This file is part of libflowmanager.
 *
 * This code has been developed by the University of Waikato WAND
 * research group. For further information please see http://www.wand.net.nz/
 *
 * libflowmanager is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * libflowmanager is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 */

#ifndef TCP_REORDER_H_
#define TCP_REORDER_H_

#include <stdint.h>

//#include <libtrace.h>

#ifdef __cplusplus
extern "C" {
#endif

/*@ inductive tcp_type = ignore | syn | ack | fin | rst | data | retransmit; @*/

/* Used to distinguish between different TCP events */
typedef enum {
	/* Not a valid TCP packet - do not attempt to reorder */
	TCP_REORDER_IGNORE,
	
	/* TCP SYN packet */
	TCP_REORDER_SYN,

	/* TCP ACK packet without piggybacked data */
	TCP_REORDER_ACK,

	/* TCP FIN packet */
	TCP_REORDER_FIN,

	/* TCP RST packet */
	TCP_REORDER_RST,

	/* TCP packet bearing payload */
	TCP_REORDER_DATA,

	/* Retransmitted TCP packet */
	TCP_REORDER_RETRANSMIT
} tcp_reorder_t;

/*@ predicate tcp_reorder_tp(tcp_reorder_t o, tcp_type t) =
	switch(t) {
	  case ignore : return o == TCP_REORDER_IGNORE;
	  case syn : return o == TCP_REORDER_SYN;
	  case ack : return o == TCP_REORDER_ACK;
	  case fin : return o == TCP_REORDER_FIN;
	  case rst : return o == TCP_REORDER_RST;
	  case data : return o == TCP_REORDER_DATA;
	  case retransmit : return o == TCP_REORDER_RETRANSMIT;
	};
  @*/


/* An entry in the reordering list for a TCP packet */
typedef struct tcp_pkt {

	/* The type of TCP packet */
	tcp_reorder_t type;

	/* The sequence number of the packet */
	uint32_t seq;

	/* The size of the packet payload (i.e. post-TCP header) */
	uint32_t plen;

	/* The timestamp of the packet */
	double ts;

	/* Pointer to packet data extracted via a read callback */
	void *data;
	
	/* Pointer to the next packet in the reordering list */
	struct tcp_pkt *next;

} tcp_packet_t;

//Macro in stdint give error because of target-dependent type
#define UINT32_MAX 4294967295UL 

//The comparison function is essentially arbitrary, but we want an abstract notion
//of comparison so that we don't have to manually reason about modulo the whole time
//TODO: can relate this to modulo if we want but will need extra lemmas
/*@ fixpoint int cmp(int a, int b) {
      return (a == b) ? 0 : ((a > b) ? (a - b) : (UINT32_MAX - ((b - a) - 1)));
}

	/*lemma void cmp_rev(int a, int b) 
	requires (0 <= a) && (a <= UINT32_MAX) && (0 <= b) && (b<= UINT32_MAX);
	ensures cmp(a, b) == -cmp(b, a); //not true ugh
	{
		if(a == b) {}
		else if(a > b) {assert(a-b == -(b-a));}
		else {assert(b - a )}
	}*/

@*/

/*@
// We want to say that the list (of sequence numbers) is (strongly) sorted. We define a sorted predicate and a function to insert into a sorted list

 	fixpoint bool sorted(list<int> l) {
		switch(l) {
			case nil: return true;
			case cons(h, t): return switch(t) {
						case nil: return true;
						case cons(h', t'): return cmp(h', h) >= 0 && sorted(t);
					};
		}
    }
    
    fixpoint list<int> insert(int x, list<int> l) {
    	switch(l) {
    		case nil: return cons(x, nil);
    		case cons(h, t): return cmp(h, x) >= 0 ? cons(x, l) : cons(h, insert(x, t));
    	}
    }
    
    // insert preserves sortedness
    lemma void insert_sorted(int x, list<int> l) 
    requires sorted(l) == true;
    ensures sorted(insert(x, l)) == true;
    {
    	switch(l) {
    		case nil: assert(sorted(insert(x, l)) == true);
    		case cons(h, t): 
    			if(cmp(h, x) >= 0) {assert(sorted(insert(x, l)) == true);}
    			else {
    				switch(t) {
    					case nil:
    					assert(insert(x, l) == cons(h, cons(x, nil)));
    					//how to layer the cmp and destruct?
    					  assert(sorted(insert(x, l)) == true);
    					case cons(h', t'):
    						insert_sorted(x, t);
    						assert(sorted(insert(x, l)) == true);	
    				}
    			}
    	}
    }
    
    //Now we want to define the notion of upper and lower bounds on a list, with the following:
    //NOTE: cannot define with forall because of lack of partial application
    //upper bound
    fixpoint bool ub(int x, list<int> l) {
    	switch(l) {
    		case nil: return true;
    		case cons(h, t): return cmp(x, h) >= 0 && ub(x, t);
    	}
    }
    
    fixpoint bool lb(int x, list<int> l) {
    	switch(l) {
    		case nil: return true;
    		case cons(h, t): return cmp(h, x) >= 0 && lb(x, t);
    	}
    }
    
    //Lemmas about sorting and bounds:
    
    
    

@*/
	

//TODO: for now, ignore data field except via exists
//TODO: may need malloc nodes, cases for null start and end (or in tcp_reorder/separate predicate)
//TODO: need to handle type now that this may not exist (maybe separate into 2 predicates?)

//For packets, which form a list, we want to reason about a "partial" list - from a to b, where are nodes are sorted in this list
//TODO: include type info in here
/*@ predicate tcp_packet_partial(tcp_packet_t *start, tcp_packet_t *end, int length, int bound, tcp_type type, int seq) =
	start != 0 &*& malloc_block_tcp_pkt(start) &*& start->type |-> ?t &*& start->seq |-> seq &*& start->plen |-> ?plen &*& start->ts |-> ?ts 
	&*& start->data |-> ?data &*& malloc_block(data, plen) &*& chars(data, plen, _) &*&
	// sortedness comes from here:
	cmp(seq, bound) > 0 &*& 
	start->next |-> ?next &*&
	(start == end ? length == 1 : next != 0 &*& tcp_packet_partial(next, end, length-1, seq, ?type1, ?seq1));
	      //TODO: can we make more general by quantifying over the bound for next one?

@*/
//The overall predicate just says that additionally, the last packet points to NULL
/*@

predicate tcp_packet_full(tcp_packet_t *start, tcp_packet_t *end, int length, int bound, tcp_type type, int seq) =
	end != 0 &*& end->next |-> 0 &*&
	tcp_packet_partial(start, end, length, bound, type, seq);

@*/

/* predicate tcp_packet_tp(tcp_packet_t *start, tcp_packet_t *end, int length, int bound, tcp_type type, int seq, int plen, double ts) =
	      end != 0 &*&
	      malloc_block_tcp_pkt(start) &*&
	      start->type |-> ?t &*& start->seq |-> seq &*& start->plen |-> plen &*& start->ts |-> ts &*& start->data |-> ?data&*& start->next |-> ?next &*&
	      malloc_block(data, plen) &*& chars(data, plen, _) &*&
	      //sortedness comes from here:
	      cmp(seq, bound) > 0 &*& //bound < seq
	      (start == end ? next == 0 &*& length == 1 :
	       next != 0 &*& tcp_packet_tp(next, end, length-1, seq, ?type1, ?seq1, ?plen1, ?ts1));
  */

//TODO: see how to handle this
typedef struct libtrace_packet_t {} libtrace_packet_t;

//Verifast will not parse inline definition
typedef void *read_packet_callback(uint32_t exp, libtrace_packet_t *packet);

typedef void destroy_packet_callback(void *data);



/* A TCP reorderer - one is required for each half of a TCP connection */
typedef struct tcp_reorder {
	
	/* Current expected sequence number */
	uint32_t expected_seq;

	/* Number of packets in the reordering list */
	uint32_t list_len; 

	/* Read callback function for packets that are to be inserted into
	 * the reordering list */
	read_packet_callback *read_packet;
	//void *(*read_packet)(uint32_t exp, libtrace_packet_t *packet);

	/* Destroy callback function for packet data extracted using the
	 * read callback */
	destroy_packet_callback *destroy_packet;
	//void (*destroy_packet)(void *);

	/* The head of the reordering list */
	tcp_packet_t *list;

	/* The last element in the reordering list */
	tcp_packet_t *list_end;

} tcp_packet_list_t;

//TODO: see what params we need here/in the previous predicate
//TODO: include list of elements? (maybe later - need to sort it)
//TODO: malloc
/*@ predicate tcp_packet_list_tp(tcp_packet_list_t *reorder, int exp_seq, int length, tcp_packet_t *start, tcp_packet_t *end) =
      malloc_block_tcp_reorder(reorder) &*&
      reorder->expected_seq |-> exp_seq &*& reorder->list_len |-> length &*& reorder->read_packet |-> _ &*& reorder->destroy_packet |-> ?des &*&
      reorder->list |-> start &*& reorder->list_end |-> end &*&
      start == 0 ? end == 0 && length == 0 :
      tcp_packet_full(start, end, length, 0, _, _);
@*/
      

/* Creates and returns a new TCP reorderer
 *
 * Parameters:
 *      cb - a callback function to be called for each packet pushed onto the
 *           reorder
 *      destroy_cb - a callback function to be called whenever a packet is
 *                   removed from the reorderer
 *
 * Returns:
 *      a pointer to a newly allocated TCP reorderer
 */
tcp_packet_list_t *tcp_create_reorderer(read_packet_callback *cb, destroy_packet_callback *destroy_cb);
// void *(*callback)(uint32_t, libtrace_packet_t *), void (*destroy_cb)(void *));

/* Destroys a TCP reorderer, freeing any resources it may be using
 *
 * Parameters:
 *      ord - the reorderer to be destroyed
 */
void tcp_destroy_reorderer(tcp_packet_list_t *ord);

/* Pushes a libtrace packet onto a TCP reorderer
 *
 * Parameters:
 *      ord - the reorderer to push the packet onto
 *      packet - the packet to push on
 *
 * Parameters:
 *      the type of the packet - if TCP_REORDER_IGNORE, the packet was not
 *      pushed on at all and should be ignored by the caller
 */
tcp_reorder_t tcp_reorder_packet(tcp_packet_list_t *ord,
        libtrace_packet_t *packet);

/* Pops the first reordered TCP packet off the reorderer's packet list. 
 *
 * Packets are only popped if they match the current expected sequence number.
 *
 * Parameters:
 *      ord - the reorderer to pop a packet from
 *
 * Returns:
 *      a pointer to the TCP packet that matches the expected sequence number.
 *      If no such packet is currently in the reordering list, NULL is 
 *      returned.
 *
 */
tcp_packet_t *tcp_pop_packet(tcp_packet_list_t *ord);

#ifdef __cplusplus
}
#endif

#endif
