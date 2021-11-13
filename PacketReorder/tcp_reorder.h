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

//@ #include "listex.gh"

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

//NOTE: this is NOT an accurate representation of cmp because of casting. It doesn't matter for us; we don't use the
// real definition anywhere. See the Coq file for the true function and related lemmas. We take these lemmas as axioms here
// because Verifast cannot deal with intentional overflow, but we proved them in Coq
/*@ fixpoint int cmp(int a, int b);
/* {
      return (a == b) ? 0 : ((a > b) ? (a - b) : (UINT32_MAX - ((b - a) - 1)));
}
*/

    //To say anything useful about cmp, we need to ensure that all elements in the list are between 0 and 2^31-1. We do so with forall and the following fixpoint
    
    fixpoint bool inrange(int x) {
    	return (0 <= x) && (x <= INT32_MAX);
    }
    
	lemma void cmp_inj(int a, int b);
	requires (0 <= a) && (a <= UINT32_MAX) && (0 <= b) && (b <= UINT32_MAX) && cmp(a,b) == 0;
	ensures a == b;

	lemma void cmp_antisym1(int a, int b);
	requires inrange(a) == true && inrange(b) == true && cmp(a,b) > 0;
	ensures cmp(b,a) < 0; 
	
	lemma void cmp_antisym2(int a, int b);
	requires inrange(a) == true && inrange(b) == true && cmp(a,b) < 0;
	ensures cmp(b,a) > 0; 

@*/

/*@
// We want to say that the list (of sequence numbers) is (strongly) sorted. We define a sorted predicate and a function to insert into a sorted list

 	fixpoint bool sorted(list<int> l) {
		switch(l) {
			case nil: return true;
			case cons(h, t): return switch(t) {
						case nil: return true;
						case cons(h', t'): return cmp(h', h) > 0 && sorted(t);
					};
		}
    }
    
    fixpoint list<int> insert(int x, list<int> l) {
    	switch(l) {
    		case nil: return cons(x, nil);
    		case cons(h, t): return cmp(h, x) > 0 ? cons(x, l) : cons(h, insert(x, t));
    	}
    }
    
    

    
    // insert preserves sortedness
    lemma void insert_sorted(int x, list<int> l) 
    requires sorted(l) == true && forall(l, inrange) && !mem(x, l) && inrange(x) == true;
    ensures sorted(insert(x, l)) == true;
    {
    	switch(l) {
    		case nil: assert(sorted(insert(x, l)) == true);
    		case cons(h, t): 
    			if(cmp(h, x) > 0) {}
    			else if(cmp(h, x) == 0) { 
    				cmp_inj(h, x);
    			}
    			else {
    				forall_mem(h, l, inrange);
					cmp_antisym2(h, x);
    				switch(t) {
    					case nil:
    					case cons(h', t'):
    						insert_sorted(x, t);
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
//TODO: need to handle type now that this may not exist (maybe separate into 2 predicates?)

//For packets, which form a list, we  want to reason about a "partial" list - from a to b, where are nodes are sorted in this list
//TODO: include type info in here

//TODO: This is kind of ugly, but we need to be able to separate out the end->seq part and not just have it in the recursive predicate
//Otherwise, we cannot use end->seq in any lemmas, and we need to do this for upper bounding the list contents
/*@ 
	predicate tcp_packet_partial(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq) =
	start != 0 &*& end != 0 &*&
	end->seq |-> end_seq &*& end->next |-> end_next &*& inrange(end_seq) == true &*& tcp_packet_partial_aux(start, end, contents, seq);

	predicate tcp_packet_partial_aux(tcp_packet_t *start, tcp_packet_t *end, list<int> contents, int seq) =
	// start is properly intialized
	start != 0 &*& malloc_block_tcp_pkt(start) &*& 
	//fields are initialized
	start->type |-> ?t &*& start->plen |-> ?plen &*& start->ts |-> ?ts &*& 
	// data is initialized
	start->data |-> ?data &*& malloc_block(data, plen) &*& chars(data, plen, _) &*& 
	// sortedness/contents
	sorted(contents) == true &*& contents == cons(?h, ?tl) &*& seq == h &*&
	// predicate recursively holds - only handle seq and next in recursive case because we handle end separately
	(start == end ? tl == nil: start->next |-> ?next &*& next != 0 &*& inrange(seq) == true &*& start->seq |-> seq &*& tcp_packet_partial_aux(next, end, tl, ?seq1));

@*/
//The overall predicate just says that additionally, the last packet points to NULL
/*@
//TODO: do we need end_seq visible?
predicate tcp_packet_full(tcp_packet_t *start, tcp_packet_t *end, list<int> contents, int seq) =
	end != 0 &*& tcp_packet_partial(start, end, 0, contents, seq, ?end_seq);

@*/

/*@
	//We need a few lemmas about tcp_packet_partial:
	
	//First, the end node is always non-NULL (needs to be done in 3 stages)
	lemma void partial_aux_end_nonnull(tcp_packet_t *start, tcp_packet_t *end)
	requires tcp_packet_partial_aux(start, end, ?contents, ?seq);
	ensures tcp_packet_partial_aux(start, end, contents, seq) &*& end != 0;
	{
		open tcp_packet_partial_aux(start, end, contents, seq);
		if(start == end) {
		} else {
			partial_aux_end_nonnull(start->next, end);
		}
		close tcp_packet_partial_aux(start, end, contents, seq);
	}
	
	lemma void partial_end_nonnull(tcp_packet_t *start, tcp_packet_t *end)
	requires tcp_packet_partial(start, end, ?next, ?contents, ?seq, ?end_seq);
	ensures tcp_packet_partial(start, end, next, contents, seq, end_seq) &*& end != 0;
	{
		open tcp_packet_partial(start, end, next, contents, seq, end_seq);
		partial_aux_end_nonnull(start, end);
		close tcp_packet_partial(start, end, next, contents, seq, end_seq);
	}
	
	lemma void full_end_nonnull(tcp_packet_t *start, tcp_packet_t *end)
	requires tcp_packet_full(start, end, ?contents, ?seq);
	ensures tcp_packet_full(start, end, contents, seq) &*& end != 0;
	{
		open tcp_packet_full(start, end, contents, seq);
		partial_end_nonnull(start, end);
		close tcp_packet_full(start, end, contents, seq);
	}
	
	//Now, we need to know that all values in the contents list are upper bounded by end->seq
	lemma void partial_contents_ub(tcp_packet_t *start, tcp_packet_t *end)
	requires tcp_packet_partial(start, end, ?next, ?contents, ?seq, ?end_seq);
	ensures tcp_packet_partial(start, end, next, contents, seq, end_seq) &*& ub(end_seq, contents) == true;
	{
		assume(false);
	}

@*/



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

//TODO: maybe change params but I think ok (maybe can say something about create/destroy to deal with that, maybe not)
/*@ predicate tcp_packet_list_tp(tcp_packet_list_t *reorder, list<int> contents, tcp_packet_t *start, tcp_packet_t *end) =
      malloc_block_tcp_reorder(reorder) &*&
      //fields initialized
      reorder->expected_seq |-> _ &*& reorder->list_len |-> ?length &*& reorder->read_packet |-> _ &*& reorder->destroy_packet |-> _ &*&
      reorder->list |-> start &*& reorder->list_end |-> end &*& length(contents) == length &*&
      // either empty or well-formed packet
      start == 0 ? end == 0 && contents == nil:
       	tcp_packet_full(start, end, contents, _);
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
