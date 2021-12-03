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
#include "in.h" //In real code, this is netinet/in.h, but we want to give specs for ntohl and htons

//@ #include "listex.gh"
//@ #include "sort.gh"
//@ #include "tcp_semantics.gh"

#include "libtrace.h"

#ifdef __cplusplus
extern "C" {
#endif


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

/*@

//Relate tcp_reorder_effect to this enum

//switch statement does not work on enums in fixpoint functions
fixpoint tcp_reorder_effect reorder_t_to_effect(tcp_reorder_t re) {
	return 
	re == TCP_REORDER_IGNORE ? r_ignore :
	re == TCP_REORDER_SYN ? r_syn :
	re == TCP_REORDER_FIN ? r_fin :
	re == TCP_REORDER_ACK ? r_ack :
	re == TCP_REORDER_RST ? r_rst :
	re == TCP_REORDER_DATA ? r_data : r_retransmit;
}

fixpoint tcp_reorder_t effect_to_reorder_t (tcp_reorder_effect eff) {
	switch(eff) {
		case r_ignore: return TCP_REORDER_IGNORE;
		case r_syn: return TCP_REORDER_SYN;
		case r_ack: return TCP_REORDER_ACK;
		case r_fin: return TCP_REORDER_FIN;
		case r_rst: return TCP_REORDER_RST;
		case r_data: return TCP_REORDER_DATA;
		case r_retransmit: return TCP_REORDER_RETRANSMIT;
	}
}

//These are inverses of each other:

fixpoint bool valid_reorder_t(tcp_reorder_t re) {
	//This is easier for Verifast than the obvious 0 <= re <= 6
	return re == 0 || re == 1 || re == 2 || re == 3 || re == 4 || re == 5 || re ==6;
	//return 0 <= re && re <= 6;
}

lemma void reorder_t_effect_inv(tcp_reorder_t re)
requires valid_reorder_t(re) == true;
ensures re == effect_to_reorder_t(reorder_t_to_effect(re));
{
	switch(re) {
		case TCP_REORDER_IGNORE:
		case TCP_REORDER_SYN:
		case TCP_REORDER_ACK:
		case TCP_REORDER_FIN:
		case TCP_REORDER_RST:
		case TCP_REORDER_DATA:
		case TCP_REORDER_RETRANSMIT: break;
		default: assert valid_reorder_t(re) == false;
	}
}

lemma void effect_reorder_t_inv(tcp_reorder_effect eff)
requires true;
ensures eff == reorder_t_to_effect(effect_to_reorder_t(eff));
{
	switch(eff) {
		case r_ignore:
		case r_syn:
		case r_ack:
		case r_fin:
		case r_rst:
		case r_data:
		case r_retransmit:
	}
}

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

/*@
//To handle the callbacks, we need to give specifications. To ensure that information is allocated and free'd, we give abstract head predictate data_present, which is
//created when a read_packet_callback is called and destroyed when destroy_packet_callback is called.

predicate data_present(void *data);

@*/
//Verifast will not parse inline definition
//NOTE: we require that result != 0 (or else the TCP reorderer will ignore the packet). This is not strictly necessary; it's just a trivial case and it simplifies the specs.
typedef void *read_packet_callback(uint32_t exp, libtrace_packet_t *packet);
//@ requires inrange(exp) == true;
//@ ensures result != 0 &*& data_present(result);

typedef void destroy_packet_callback(void *data);
//@ requires data_present(data);
//@ ensures true;
	

//TODO: for now, ignore data field except via exists
//TODO: need to handle type now that this may not exist (maybe separate into 2 predicates?)

//For packets, which form a list, we  want to reason about a "partial" list - from a to b, where are nodes are sorted in this list
//TODO: include type info in here


/*@ 

//These are the non-list parts of the packet
predicate tcp_packet_single(tcp_packet_t *start, int seq, tcp_reorder_effect eff) =
// start is properly intialized
start != 0 &*& malloc_block_tcp_pkt(start) &*& 
//fields are initialized
start->type |-> effect_to_reorder_t(eff) &*& start->plen |-> ?plen &*& start->ts |-> ?ts &*& 
// data is initialized
start->data |-> ?data &*& data_present(data) &*& 
//seq
start->seq |-> seq &*& inrange(seq) == true;

// This is the natural way to express a linked list with start and end pointers. It is useful for getting information about the start node, but not the end node.
//TODO: HERE
predicate tcp_packet_partial(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq, tcp_reorder_effect eff) =
tcp_packet_single(start, seq, eff) &*& start->next |-> ?next &*&
// sortedness/contents
sorted(contents) == true &*& contents == cons(pair(seq, eff), ?tl) &*&
// predicate recursively holds - only handle seq and next in recursive case because we handle end separately
(start == end ? tl == nil && next == end_next: next != 0 &*& tcp_packet_partial(next, end, end_next, tl, ?seq1, ?eff1));

//Alternatively, in most cases, we instead need to access the end packet (and crucially, sequence number). We define an alternate partial predicate and then prove equivalence in partial.gh:

predicate tcp_packet_partial_end(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq, 
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff) =
tcp_packet_single(end, end_seq, end_eff) &*& end != 0 &*& end->next |-> end_next &*& sorted(contents) == true &*&
(start == end ? contents == cons(pair(end_seq, end_eff), nil) && seq == end_seq && eff == end_eff
: contents != nil &*& tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq, eff) &*& drop(length(contents) - 1, contents) == cons(pair(end_seq, end_eff), nil)); 

//Due to a Verifast limitation (related to when we can use patterns), we want a more general predicate that allows us to describe an empty list:
predicate tcp_packet_partial_end_gen(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq, 
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff) =
	start != 0 && end != 0 ? tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) : contents == nil; 
	
//The overall predicate just says that additionally, the last packet points to NULL

predicate tcp_packet_full(tcp_packet_t *start, tcp_packet_t *end, list<pair<int, tcp_reorder_effect> > contents, int seq) =
	end != 0 &*& tcp_packet_partial(start, end, 0, contents, seq, ?eff);

@*/


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
/*@

	//All of the non-contents/start parts of a tcp reorderer, which we bundle together because most are not changing. This is mostly helpful for the loop invariant in insert,
	//since we need ord->list but the others are not accessed.
	predicate tcp_packet_list_wf(tcp_packet_list_t *reorder, tcp_packet_t *end, int length, int exp_seq) =
		malloc_block_tcp_reorder(reorder) &*&
      		//fields initialized
      		reorder->expected_seq |-> exp_seq &*& reorder->list_len |-> length &*& reorder->read_packet |-> ?rp &*& reorder->destroy_packet |-> ?dp &*&
      		is_read_packet_callback(rp) == true &*& 
      		dp != 0 &*& is_destroy_packet_callback(dp) == true &*&
      		inrange(exp_seq) == true &*&
      		reorder->list_end |-> end;
		
	//We don't need to expose start and end; we only care about the contents and the expected sequence number
 	predicate tcp_packet_list_tp(tcp_packet_list_t *reorder, list<pair<int, tcp_reorder_effect> > contents, int exp_seq) =
		tcp_packet_list_wf(reorder, ?end, length(contents), exp_seq) &*& reorder->list |-> ?start &*&
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
/*@

/* Lemmas for Manipulating the tcp_packet_partial Predicates */

/* Helper lemmas */

// The start node is non-null in any partial list
lemma void partial_start_nonzero(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff)
requires tcp_packet_partial(start, end, end_next, contents, seq, eff);
ensures tcp_packet_partial(start, end, end_next, contents, seq, eff) &*& start != 0;
{
	open tcp_packet_partial(start, end, end_next, contents, seq, eff);
	open tcp_packet_single(start, seq, eff);
	close tcp_packet_single(start, seq, eff);
	close tcp_packet_partial(start, end, end_next, contents, seq, eff);
}

// The first item in contents is seq, and contents is non-null
lemma void partial_end_contents_head(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& head(contents) == pair(seq, eff) &*& contents != nil;
{
	
	open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	if(start == end) {}
	else {
		open tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq, eff);
		length_pos(contents);
		head_take(contents, length(contents) - 1);
		close tcp_packet_partial(start, pen, end, take(length(contents) - 1, contents), seq, eff);
	}
	close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
}

/* Equivalence between tcp_packet_partial and tcp_packet_partial_end */

// This equivalence is not easy to show, since the predicates are defined quite differently. We prove each direction in the following lemmas

//tcp_packet_partial -> tcp_packet_partial_end for some end_seq
lemma void partial_start_implies_end(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff)
requires tcp_packet_partial(start, end, end_next, contents, seq, eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, ?end_seq, ?end_eff);
{
	if(start == end) {
		open tcp_packet_partial(start, end, end_next, contents, seq, eff);
		open tcp_packet_single(start, seq, eff);
		int end_seq = end->seq;
		close tcp_packet_single(end, end_seq, eff);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, eff);
	}
	else {
		open tcp_packet_partial(start, end, end_next, contents, seq, eff);
		tcp_packet_t *next = start->next;
		list<pair<int, tcp_reorder_effect> > tl = tail(contents);
		//Get next->seq as a variable
		open tcp_packet_partial(next, end, end_next, tl, ?seq1, ?eff1);
		close tcp_packet_partial(next, end, end_next, tl, seq1, eff1);
		
		partial_start_implies_end(next, end, end_next, tl, seq1, eff1);
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, eff1, ?end_seq, ?end_eff);
		if(next == end) {
			
			//get that start != 0
			open tcp_packet_single(start, seq, eff);
			close tcp_packet_single(start, seq, eff);
			
			close tcp_packet_partial(start, start, end, cons(pair(seq, eff), nil), seq, eff);
			close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		}
		else {
			//The inductive case
			//to get pen in the context
			assert(tcp_packet_partial(next, ?pen, end, take(length(tail(contents)) - 1, tail(contents)), seq1, eff1));
			sorted_app1(take(length(contents) - 1, contents), drop(length(contents) -1, contents));
			//want to show start != pen
			if(start == pen) {
				//in this case, we have start -> next -> pen = start, so we have a cycle, contradiction bc of separating conjuction
				//we need to get pen->next to show it is end, so we apply IH again
				partial_start_implies_end(next, pen, end, take((length(tail(contents)) - 1), tail(contents)), seq1, eff1);
				open tcp_packet_partial_end(next, pen, end, take((length(tail(contents)) - 1), tail(contents)), seq1, eff1, ?end_seq1, _);
			}
			else {
				close tcp_packet_partial(start, pen, end, take((length(contents) - 1), contents), seq, eff);
				close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
			}
		}
	}
}
	

//tcp_packet_partial_end -> tcp_packet_partial (easier)	
lemma void partial_end_implies_start(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial(start, end, end_next, contents, seq, eff);
{
	if(start==end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		close tcp_packet_partial(start, end, end_next, contents, seq, eff);
	}
	else {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		//get pen in context
		open tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq, eff);
		tcp_packet_t *next = start->next;
		if(start == pen) {
			close tcp_packet_partial(next, end, end_next, cons(pair(end_seq, end_eff), nil), end_seq, end_eff);
			length_pos(contents);
			append_drop_take(contents, length(contents) - 1);
			close tcp_packet_partial(start, end, end_next, contents, seq, eff);
		}
		else {
			sorted_tail(contents);
			assert(contents == cons(?seq2, tail(contents)));
			//need seq1 in context
			open tcp_packet_partial(next, pen, end, tail(take(length(contents) - 1, contents)), ?seq1, ?eff1);
			close tcp_packet_partial(next, pen, end, tail(take(length(contents) - 1, contents)), seq1, eff1);
			
			close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
			partial_end_implies_start(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
			close tcp_packet_partial(start, end, end_next, contents, seq, eff);
		}
	}
}

/* Using tcp_packet_partial_end recursively */

// While tcp_packet_partial is cleaner and more elegant as a specification, tcp_packet_partial_end is more useful because we often need to access both the start and end of the list, and we need information about end_seq.
// tcp_packet_partial is much easier to reason about inductively (due to its definition). To overcome this, we prove the following two lemmas, which let us reason about tcp_packet_partial_end inductively as well:

// This allows us to peel off the first packet and still have tcp_partial_packet_end of the remaining list so that we can apply the IH on the remaining list
lemma void tcp_partial_packet_end_ind(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& start != end;
ensures tcp_packet_single(start, seq, eff) &*& start->next |-> ?next &*& contents == cons(pair(seq, eff), ?tl) &*& 
	tcp_packet_partial_end(next, end, end_next, tl, ?seq1, ?eff1, end_seq, end_eff) &*& sorted(contents) == true;
{
	open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	open tcp_packet_partial(start, ?pen, end, take(length(contents) -1, contents), seq, eff);
	//get next in context
	open tcp_packet_single(start, seq, eff);
	tcp_packet_t *next = start->next;
	close tcp_packet_single(start, seq, eff);
	sorted_tail(contents);
	length_pos(contents);
	append_drop_take(contents, length(contents) - 1);
	if(start == pen) {
		close tcp_packet_partial_end(next, end, end_next, cons(pair(end_seq, end_eff), nil), end_seq, end_eff, end_seq, end_eff);
	}
	else {
		//get seq1 in context
		open tcp_packet_partial(next, pen, end, tail(take(length(contents) -1, contents)), ?seq1, ?eff1);
		close tcp_packet_partial(next, pen, end, tail(take(length(contents) -1, contents)), seq1, eff1); 
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
	}
}

// Then, we need to reconstruct the full list, so this lemma is essentially the converse of the previous one
	
lemma void tcp_partial_packet_end_fold(tcp_packet_t *start, tcp_packet_t *next, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int seq1, tcp_reorder_effect eff1, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_single(start, seq, eff) &*& start->next |-> next &*& contents == cons(pair(seq, eff), ?tl) &*& sorted(contents) == true &*&
 		 tcp_packet_partial_end(next, end, end_next, tl, seq1, eff1, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& start != end;
{
	if(start == end) {
		//contradiction with 2 start->next blocks
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, eff1, end_seq, end_eff);
	}
	else {
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, eff1, end_seq, end_eff);
		if(next == end) {
			close tcp_packet_partial(start, start, end, take(length(contents) - 1, contents), seq, eff);
			close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		}
		else {
			//get pen in context
			open tcp_packet_partial(next, ?pen, end, take(length(tl) - 1, tl), seq1, eff1);
			close tcp_packet_partial(next, pen, end, take(length(tl) - 1, tl), seq1, eff1);
			
			//prove sorted (TODO: make separate lemma?)
			length_pos(tl);
			append_drop_take(contents, length(contents) - 1);
			sorted_app1(take(length(contents) - 1, contents), drop(length(contents) -1, contents));
			
			//prove that next != 0
			open tcp_packet_partial(next, pen, end, take((length(tl) -1), tl), seq1, eff1);
			open tcp_packet_single(next, seq1, eff1);
			close tcp_packet_single(next, seq1, eff1);
			close tcp_packet_partial(next, pen, end, take((length(tl) -1), tl), seq1, eff1);
			
			//prove that start != pen
			if(start == pen) {
				//again, contradiction in separation logic
				partial_start_implies_end(next, pen, end, take((length(tl) - 1), tl), seq1, eff1);
				open tcp_packet_partial_end(next, pen, end, take((length(tl) - 1), tl), seq1, eff1, ?end_seq1, ?end_eff1);
			}
			else {
				close tcp_packet_partial(start, pen, end, cons(pair(seq, eff), take(length(tl) - 1, tl)), seq, eff);
				close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
			}
		}
	}
}

/* Combining list segments */

// This lemma is crucial - it lets us combine two partial_end predicates (list segments) into one complete one. The list representing the combined segment is append(l1, l2) as expected.
lemma void partial_app(tcp_packet_t *start, tcp_packet_t *p1, tcp_packet_t *p2, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > l1, 
	list<pair<int, tcp_reorder_effect> > l2, int seq1, tcp_reorder_effect eff1, int seq2, tcp_reorder_effect eff2, int end_seq1,
	tcp_reorder_effect end_eff1, int end_seq2, tcp_reorder_effect end_eff2)
requires tcp_packet_partial_end(start, p1, p2, l1, seq1, eff1, end_seq1, end_eff1) &*& tcp_packet_partial_end(p2, end, end_next, l2, seq2, eff2, end_seq2, end_eff2) &*& 
	sorted(append(l1, l2)) == true;
ensures tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, eff1, end_seq2, end_eff2);
{
	if(start == p1) {
		open tcp_packet_partial_end(start, p1, p2, l1, seq1, eff1, end_seq1, end_eff1);
		open tcp_packet_partial_end(p2, end, end_next, l2, seq2, eff2, end_seq2, end_eff2);
		if(p2 == end) {
			close tcp_packet_partial(start, start, end, take((length(append(l1, l2)) - 1), append(l1, l2)), seq1, eff1);
			close tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, eff1, end_seq2, end_eff2);
		}
		else {
			//get pen in context
			open tcp_packet_partial(p2, ?pen, end, take(length(l2) - 1, l2), seq2, eff2);
			close tcp_packet_partial(p2, pen, end, take(length(l2) - 1, l2), seq2, eff2);
			
			//need to prove sorted(seq1 :: take(length(l2) - 1, l2))
			length_pos(l2);
			append_drop_take(l2, length(l2) - 1);
			append_assoc(l1, take(length(l2) -1, l2), drop(length(l2) -1, l2));
			sorted_app1(append(l1, take(length(l2) - 1, l2)), drop(length(l2) - 1, l2));
			
			//prove p2 != 0
			partial_start_nonzero(p2, pen, end, take((length(l2) - 1), l2), seq2, eff2);
			//need to prove that start != pen
			if(start == pen) {
				//if it is, then start->next = p2 and pen->next = end, so p2 = end, contradiction
				partial_start_implies_end(p2, pen, end, take(length(l2) - 1, l2), seq2, eff2);
				open tcp_packet_partial_end(p2, pen, end, take(length(l2) - 1, l2), seq2, eff2, ?end_seq3, ?end_eff3);
			}
			else {
				close tcp_packet_partial(start, pen, end, cons(pair(seq1, eff1), take(length(l2) - 1, l2)), seq1, eff1); 
				close tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, eff1, end_seq2, end_eff2);
			}
		}
	}
	else {
		//inductive case
		tcp_partial_packet_end_ind(start, p1, p2, l1, seq1, eff1, end_seq1, end_eff1);
		//get next and seq1 in context
		tcp_packet_t *next = start->next;
		open tcp_packet_partial_end(next, p1, p2, tail(l1), ?seq12, ?eff12, end_seq1, end_eff1);
		close tcp_packet_partial_end(next, p1, p2, tail(l1), seq12, eff12, end_seq1, end_eff1);
		
		//we want to show end != next
		if(next == end) {
			//want to get end->next and next->next heap chunks to prove false (must be disjoint)
			open tcp_packet_partial_end(p2, end, end_next, l2, seq2, eff2, end_seq2, end_eff2); //end->next chunk
			//easiest way is to use previous lemma (though it's not strictly needed)
			partial_end_implies_start(next, p1, p2, tail(l1), seq12, eff12, end_seq1, end_eff1);
			open tcp_packet_partial(next, p1, p2, tail(l1), seq12, eff12);
		}
		else {
			sorted_tail(append(l1, l2));
			partial_app(next, p1, p2, end, end_next, tail(l1), l2, seq12, eff12, seq2, eff2, end_seq1, end_eff1, end_seq2, end_eff2); 
			//combine result back into full predicate
			tcp_partial_packet_end_fold(start, next, end, end_next, append(l1, l2), seq1, eff1, seq12, eff12, end_seq2, end_eff2);
		}
	}
}

/* Bounds on the contents list */

// We want to know that everything in the contents list is bounded between seq and end_seq. This requires several steps.
	
//First, we show that seq and end_seq are in the contents list
lemma void partial_end_contents_mem(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& mem(seq, map(fst, contents)) == true &*& mem(end_seq, map(fst, contents)) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		//get next and seq1 in context
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, ?eff1, end_seq, end_eff);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		
		partial_end_contents_mem(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, eff, seq1, eff1, end_seq, end_eff);
	}
}
	
// Then, we show that everything in contents is inrange (between 0 and 2^31-1). This is the real result; the following lemma is for convenience, so we don't need to call forall_mem each time.
lemma void partial_end_contents_forall_inrange(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& forall(map(fst, contents), inrange) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		open tcp_packet_single(end, end_seq, end_eff);
		close tcp_packet_single(end, end_seq, end_eff);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		open tcp_packet_single(start, seq, eff);
		close tcp_packet_single(start, seq, eff);
		
		//get next and seq1
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, ?eff1, end_seq, end_eff);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		partial_end_contents_forall_inrange(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, eff, seq1, eff1, end_seq, end_eff);
	}
}
	
	
lemma void partial_end_contents_inrange(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff, int x)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& mem(x, map(fst, contents)) == true;
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& inrange(x) == true;
{
	partial_end_contents_forall_inrange(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	forall_mem(x, map(fst, contents), inrange);
}

// Now, we can prove the upper bound; ie: everything in contents is at most end_next
	
lemma void partial_end_contents_ub(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& ub(end_seq, contents) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		cmp_same(end_seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		//get next and seq1 in context
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, ?eff1, end_seq, end_eff);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		//get IH
		partial_end_contents_ub(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		
		//need to prove that seq < seq1 - use sortedness after showing that head(contents) = seq1 
		partial_end_contents_head(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		head_tail(tail(contents));
		//need to know that end_seq and seq1 are in range, so we can use transitivity (we get that cmp(seq1, seq) > 0 by sortedness and the rest from the upper bound)
		partial_end_contents_mem(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff);
		partial_end_contents_inrange(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff, end_seq);
		partial_end_contents_inrange(next, end, end_next, tail(contents), seq1, eff1, end_seq, end_eff, seq1);
		//need to know seq is in range
		open tcp_packet_single(start, seq, eff);
		close tcp_packet_single(start, seq, eff);
		cmp_ge_trans(end_seq, seq1, seq);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, eff, seq1, eff1, end_seq, end_eff);
	}
}

//One other helpful lemma: the head of partial_end is always nonzero
lemma void partial_end_start_nonzero(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<pair<int, tcp_reorder_effect> > contents, int seq,
	tcp_reorder_effect eff, int end_seq, tcp_reorder_effect end_eff)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff) &*& start != 0;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		open tcp_packet_single(start, seq, eff);
		close tcp_packet_single(start, seq, eff);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, eff, end_seq, end_eff);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, eff, end_seq, end_eff);
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?next_seq, ?next_eff, end_seq, end_eff);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), next_seq, next_eff, end_seq, end_eff);
		open tcp_packet_single(start, seq, eff);
		close tcp_packet_single(start, seq, eff);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, eff, next_seq, next_eff, end_seq, end_eff);
	}
}
@*/

#endif
