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
predicate tcp_packet_single(tcp_packet_t *start, int seq) =
// start is properly intialized
start != 0 &*& malloc_block_tcp_pkt(start) &*& 
//fields are initialized
start->type |-> ?t &*& start->plen |-> ?plen &*& start->ts |-> ?ts &*& 
// data is initialized
start->data |-> ?data &*& data_present(data) &*& 
//seq
start->seq |-> seq &*& inrange(seq) == true;

// This is the natural way to express a linked list with start and end pointers. It is useful for getting information about the start node, but not the end node.

predicate tcp_packet_partial(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq) =
tcp_packet_single(start, seq) &*& start->next |-> ?next &*&
// sortedness/contents
sorted(contents) == true &*& contents == cons(?h, ?tl) &*& seq == h &*&
// predicate recursively holds - only handle seq and next in recursive case because we handle end separately
(start == end ? tl == nil && next == end_next: next != 0 &*& tcp_packet_partial(next, end, end_next, tl, ?seq1));

//Alternatively, in most cases, we instead need to access the end packet (and crucially, sequence number). We define an alternate partial predicate and then prove equivalence in partial.gh:

predicate tcp_packet_partial_end(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq) =
tcp_packet_single(end, end_seq) &*& end != 0 &*& end->next |-> end_next &*& sorted(contents) == true &*&
(start == end ? contents == cons(end_seq, nil) && seq == end_seq
: contents != nil &*& tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq) &*& drop(length(contents) - 1, contents) == cons(end_seq, nil)); 

//Due to a Verifast limitation (related to when we can use patterns), we want a more general predicate that allows us to describe an empty list:
predicate tcp_packet_partial_end_gen(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq) =
	start != 0 && end != 0 ? tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) : contents == nil; 
	
	
//The overall predicate just says that additionally, the last packet points to NULL

predicate tcp_packet_full(tcp_packet_t *start, tcp_packet_t *end, list<int> contents, int seq) =
	end != 0 &*& tcp_packet_partial(start, end, 0, contents, seq);

@*/



//TODO: see how to handle this
//typedef struct libtrace_packet_t {} libtrace_packet_t;


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
 	predicate tcp_packet_list_tp(tcp_packet_list_t *reorder, list<int> contents, int exp_seq) =
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
lemma void partial_start_nonzero(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq)
requires tcp_packet_partial(start, end, end_next, contents, seq);
ensures tcp_packet_partial(start, end, end_next, contents, seq) &*& start != 0;
{
	open tcp_packet_partial(start, end, end_next, contents, seq);
	open tcp_packet_single(start, seq);
	close tcp_packet_single(start, seq);
	close tcp_packet_partial(start, end, end_next, contents, seq);
}

// The first item in contents is seq, and contents is non-null
lemma void partial_end_contents_head(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& head(contents) == seq &*& contents != nil;
{
	
	open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	if(start == end) {}
	else {
		open tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq);
		length_pos(contents);
		head_take(contents, length(contents) - 1);
		close tcp_packet_partial(start, pen, end, take(length(contents) - 1, contents), seq);
	}
	close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
}

/* Equivalence between tcp_packet_partial and tcp_packet_partial_end */

// This equivalence is not easy to show, since the predicates are defined quite differently. We prove each direction in the following lemmas

//tcp_packet_partial -> tcp_packet_partial_end for some end_seq
lemma void partial_start_implies_end(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq)
requires tcp_packet_partial(start, end, end_next, contents, seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, ?end_seq);
{
	if(start == end) {
		open tcp_packet_partial(start, end, end_next, contents, seq);
		open tcp_packet_single(start, seq);
		int end_seq = end->seq;
		close tcp_packet_single(end, end_seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	}
	else {
		open tcp_packet_partial(start, end, end_next, contents, seq);
		tcp_packet_t *next = start->next;
		list<int> tl = tail(contents);
		//Get next->seq as a variable
		open tcp_packet_partial(next, end, end_next, tl, ?seq1);
		close tcp_packet_partial(next, end, end_next, tl, seq1);
		
		partial_start_implies_end(next, end, end_next, tl, seq1);
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, ?end_seq);
		if(next == end) {
			
			//get that start != 0
			open tcp_packet_single(start, seq);
			close tcp_packet_single(start, seq);
			
			close tcp_packet_partial(start, start, end, cons(seq, nil), seq);
			close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		}
		else {
			//The inductive case
			//to get pen in the context
			assert(tcp_packet_partial(next, ?pen, end, take(length(tail(contents)) - 1, tail(contents)), seq1));
			sorted_app1(take(length(contents) - 1, contents), drop(length(contents) -1, contents));
			//want to show start != pen
			if(start == pen) {
				//in this case, we have start -> next -> pen = start, so we have a cycle, contradiction bc of separating conjuction
				//we need to get pen->next to show it is end, so we apply IH again
				partial_start_implies_end(next, pen, end, take((length(tail(contents)) - 1), tail(contents)), seq1);
				open tcp_packet_partial_end(next, pen, end, take((length(tail(contents)) - 1), tail(contents)), seq1, ?end_seq1);
			}
			else {
				close tcp_packet_partial(start, pen, end, take((length(contents) - 1), contents), seq);
				close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
			}
		}
	}
}
	

//tcp_packet_partial_end -> tcp_packet_partial (easier)	
lemma void partial_end_implies_start(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial(start, end, end_next, contents, seq);
{
	if(start==end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		close tcp_packet_partial(start, end, end_next, contents, seq);
	}
	else {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		//get pen in context
		open tcp_packet_partial(start, ?pen, end, take(length(contents) - 1, contents), seq);
		tcp_packet_t *next = start->next;
		if(start == pen) {
			close tcp_packet_partial(next, end, end_next, cons(end_seq, nil), end_seq);
			length_pos(contents);
			append_drop_take(contents, length(contents) - 1);
			close tcp_packet_partial(start, end, end_next, contents, seq);
		}
		else {
			sorted_tail(contents);
			assert(contents == cons(?seq2, tail(contents)));
			//need seq1 in context
			open tcp_packet_partial(next, pen, end, tail(take(length(contents) - 1, contents)), ?seq1);
			close tcp_packet_partial(next, pen, end, tail(take(length(contents) - 1, contents)), seq1);
			
			close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, end_seq);
			partial_end_implies_start(next, end, end_next, tail(contents), seq1, end_seq);
			close tcp_packet_partial(start, end, end_next, contents, seq);
		}
	}
}

/* Using tcp_packet_partial_end recursively */

// While tcp_packet_partial is cleaner and more elegant as a specification, tcp_packet_partial_end is more useful because we often need to access both the start and end of the list, and we need information about end_seq.
// tcp_packet_partial is much easier to reason about inductively (due to its definition). To overcome this, we prove the following two lemmas, which let us reason about tcp_packet_partial_end inductively as well:

// This allows us to peel off the first packet and still have tcp_partial_packet_end of the remaining list so that we can apply the IH on the remaining list
lemma void tcp_partial_packet_end_ind(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& start != end;
ensures tcp_packet_single(start, seq) &*& start->next |-> ?next &*& contents == cons(seq, ?tl) &*& tcp_packet_partial_end(next, end, end_next, tl, ?seq1, end_seq) 
		&*& sorted(contents) == true;
{
	open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	open tcp_packet_partial(start, ?pen, end, take(length(contents) -1, contents), seq);
	//get next in context
	open tcp_packet_single(start, seq);
	tcp_packet_t *next = start->next;
	close tcp_packet_single(start, seq);
	sorted_tail(contents);
	length_pos(contents);
	append_drop_take(contents, length(contents) - 1);
	if(start == pen) {
		close tcp_packet_partial_end(next, end, end_next, cons(end_seq, nil), end_seq, end_seq);
	}
	else {
		//get seq1 in context
		open tcp_packet_partial(next, pen, end, tail(take(length(contents) -1, contents)), ?seq1);
		close tcp_packet_partial(next, pen, end, tail(take(length(contents) -1, contents)), seq1); 
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, end_seq);
	}
}

// Then, we need to reconstruct the full list, so this lemma is essentially the converse of the previous one
	
lemma void tcp_partial_packet_end_fold(tcp_packet_t *start, tcp_packet_t *next, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int seq1, int end_seq)
requires tcp_packet_single(start, seq) &*& start->next |-> next &*& contents == cons(seq, ?tl) &*& sorted(contents) == true &*&
 		 tcp_packet_partial_end(next, end, end_next, tl, seq1, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& start != end;
{
	if(start == end) {
		//contradiction with 2 start->next blocks
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, end_seq);
	}
	else {
		open tcp_packet_partial_end(next, end, end_next, tl, seq1, end_seq);
		if(next == end) {
			close tcp_packet_partial(start, start, end, take(length(contents) - 1, contents), seq);
			close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		}
		else {
			//get pen in context
			open tcp_packet_partial(next, ?pen, end, take(length(tl) - 1, tl), seq1);
			close tcp_packet_partial(next, pen, end, take(length(tl) - 1, tl), seq1);
			
			//prove sorted (TODO: make separate lemma?)
			length_pos(tl);
			append_drop_take(contents, length(contents) - 1);
			sorted_app1(take(length(contents) - 1, contents), drop(length(contents) -1, contents));
			
			//prove that next != 0
			open tcp_packet_partial(next, pen, end, take((length(tl) -1), tl), seq1);
			open tcp_packet_single(next, seq1);
			close tcp_packet_single(next, seq1);
			close tcp_packet_partial(next, pen, end, take((length(tl) -1), tl), seq1);
			
			//prove that start != pen
			if(start == pen) {
				//again, contradiction in separation logic
				partial_start_implies_end(next, pen, end, take((length(tl) - 1), tl), seq1);
				open tcp_packet_partial_end(next, pen, end, take((length(tl) - 1), tl), seq1, ?end_seq1);
			}
			else {
				close tcp_packet_partial(start, pen, end, cons(seq, take(length(tl) - 1, tl)), seq);
				close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
			}
		}
	}
}

/* Combining list segments */

// This lemma is crucial - it lets us combine two partial_end predicates (list segments) into one complete one. The list representing the combined segment is append(l1, l2) as expected.
lemma void partial_app(tcp_packet_t *start, tcp_packet_t *p1, tcp_packet_t *p2, tcp_packet_t *end, tcp_packet_t *end_next, list<int> l1, list<int> l2, 
	int seq1, int seq2, int end_seq1, int end_seq2)
requires tcp_packet_partial_end(start, p1, p2, l1, seq1, end_seq1) &*& tcp_packet_partial_end(p2, end, end_next, l2, seq2, end_seq2) &*& sorted(append(l1, l2)) == true;
ensures tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, end_seq2);
{
	if(start == p1) {
		open tcp_packet_partial_end(start, p1, p2, l1, seq1, end_seq1);
		open tcp_packet_partial_end(p2, end, end_next, l2, seq2, end_seq2);
		if(p2 == end) {
			close tcp_packet_partial(start, start, end, take((length(append(l1, l2)) - 1), append(l1, l2)), seq1);
			close tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, end_seq2);
		}
		else {
			//get pen in context
			open tcp_packet_partial(p2, ?pen, end, take(length(l2) - 1, l2), seq2);
			close tcp_packet_partial(p2, pen, end, take(length(l2) - 1, l2), seq2);
			
			//need to prove sorted(seq1 :: take(length(l2) - 1, l2))
			length_pos(l2);
			append_drop_take(l2, length(l2) - 1);
			append_assoc(l1, take(length(l2) -1, l2), drop(length(l2) -1, l2));
			sorted_app1(append(l1, take(length(l2) - 1, l2)), drop(length(l2) - 1, l2));
			
			//prove p2 != 0
			partial_start_nonzero(p2, pen, end, take((length(l2) - 1), l2), seq2);
			//need to prove that start != pen
			if(start == pen) {
				//if it is, then start->next = p2 and pen->next = end, so p2 = end, contradiction
				partial_start_implies_end(p2, pen, end, take(length(l2) - 1, l2), seq2);
				open tcp_packet_partial_end(p2, pen, end, take(length(l2) - 1, l2), seq2, ?end_seq3);
			}
			else {
				close tcp_packet_partial(start, pen, end, cons(seq1,take(length(l2) - 1, l2)), seq1); 
				close tcp_packet_partial_end(start, end, end_next, append(l1, l2), seq1, end_seq2);
			}
		}
	}
	else {
		//inductive case
		tcp_partial_packet_end_ind(start, p1, p2, l1, seq1, end_seq1);
		//get next and seq1 in context
		tcp_packet_t *next = start->next;
		open tcp_packet_partial_end(next, p1, p2, tail(l1), ?seq12, end_seq1);
		close tcp_packet_partial_end(next, p1, p2, tail(l1), seq12, end_seq1);
		
		//we want to show end != next
		if(next == end) {
			//want to get end->next and next->next heap chunks to prove false (must be disjoint)
			open tcp_packet_partial_end(p2, end, end_next, l2, seq2, end_seq2); //end->next chunk
			//easiest way is to use previous lemma (though it's not strictly needed)
			partial_end_implies_start(next, p1, p2, tail(l1), seq12, end_seq1);
			open tcp_packet_partial(next, p1, p2, tail(l1), seq12);
		}
		else {
			sorted_tail(append(l1, l2));
			partial_app(next, p1, p2, end, end_next, tail(l1), l2, seq12, seq2, end_seq1, end_seq2); 
			//combine result back into full predicate
			tcp_partial_packet_end_fold(start, next, end, end_next, append(l1, l2), seq1, seq12, end_seq2);
		}
	}
}

/* Bounds on the contents list */

// We want to know that everything in the contents list is bounded between seq and end_seq. This requires several steps.
	
//First, we show that seq and end_seq are in the contents list
lemma void partial_end_contents_mem(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& mem(seq, contents) == true &*& mem(end_seq, contents) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, end_seq);
		//get next and seq1 in context
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, end_seq);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, end_seq);
		
		partial_end_contents_mem(next, end, end_next, tail(contents), seq1, end_seq);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, seq1, end_seq);
	}
}
	
// Then, we show that everything in contents is inrange (between 0 and 2^31-1). This is the real result; the following lemma is for convenience, so we don't need to call forall_mem each time.
lemma void partial_end_contents_forall_inrange(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& forall(contents, inrange) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		open tcp_packet_single(end, end_seq);
		close tcp_packet_single(end, end_seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, end_seq);
		open tcp_packet_single(start, seq);
		close tcp_packet_single(start, seq);
		
		//get next and seq1
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, end_seq);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, end_seq);
		partial_end_contents_forall_inrange(next, end, end_next, tail(contents), seq1, end_seq);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, seq1, end_seq);
	}
}
	
	
lemma void partial_end_contents_inrange(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq, int x)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& mem(x, contents) == true;
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& inrange(x) == true;
{
	partial_end_contents_forall_inrange(start, end, end_next, contents, seq, end_seq);
	forall_mem(x, contents, inrange);
}

// Now, we can prove the upper bound; ie: everything in contents is at most end_next
	
lemma void partial_end_contents_ub(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& ub(end_seq, contents) == true;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		cmp_same(end_seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, end_seq);
		//get next and seq1 in context
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?seq1, end_seq);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), seq1, end_seq);
		//get IH
		partial_end_contents_ub(next, end, end_next, tail(contents), seq1, end_seq);
		
		//need to prove that seq < seq1 - use sortedness after showing that head(contents) = seq1 
		partial_end_contents_head(next, end, end_next, tail(contents), seq1, end_seq);
		head_tail(tail(contents));
		//need to know that end_seq and seq1 are in range, so we can use transitivity (we get that cmp(seq1, seq) > 0 by sortedness and the rest from the upper bound)
		partial_end_contents_mem(next, end, end_next, tail(contents), seq1, end_seq);
		partial_end_contents_inrange(next, end, end_next, tail(contents), seq1, end_seq, end_seq);
		partial_end_contents_inrange(next, end, end_next, tail(contents), seq1, end_seq, seq1);
		//need to know seq is in range
		open tcp_packet_single(start, seq);
		close tcp_packet_single(start, seq);
		cmp_ge_trans(end_seq, seq1, seq);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, seq1, end_seq);
	}
}

//One other helpful lemma: the head of partial_end is always nonzero
lemma void partial_end_start_nonzero(tcp_packet_t *start, tcp_packet_t *end, tcp_packet_t *end_next, list<int> contents, int seq, int end_seq)
requires tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
ensures tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq) &*& start != 0;
{
	if(start == end) {
		open tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
		open tcp_packet_single(start, seq);
		close tcp_packet_single(start, seq);
		close tcp_packet_partial_end(start, end, end_next, contents, seq, end_seq);
	}
	else {
		tcp_partial_packet_end_ind(start, end, end_next, contents, seq, end_seq);
		open tcp_packet_partial_end(?next, end, end_next, tail(contents), ?next_seq, end_seq);
		close tcp_packet_partial_end(next, end, end_next, tail(contents), next_seq, end_seq);
		open tcp_packet_single(start, seq);
		close tcp_packet_single(start, seq);
		tcp_partial_packet_end_fold(start, next, end, end_next, contents, seq, next_seq, end_seq);
	}
}
@*/

/*@ 
//TCP/IP Reordering + Semantics

/* 
Expected Sequence Number

In the reorderer, the expected sequence number describes the next byte that has not yet been fully processed; ie: all bytes before exp_seq have been
processed in order (inserted and popped from the reorderer). Different type of packets will trigger different events that update the expected
sequence number based on the TCP semantics. The following type describes these events: 
*/

inductive tcp_reorder_effect = r_ignore | r_syn | r_ack | r_fin | r_rst | r_data | r_retransmit;

//Relate this effect to the enum

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


/*
How do we know what packet should trigger which effect?
The semantics of these effects are as follows:
1. If the packet type is SYN, this packet starts the flow, so it has effect r_syn.
2. If the packet type is ACK and it has no data, it has effect r_ack. We don't need to worry about sequence number comparison here, since this packet does not
	effect the sequence numbers at all. When popped, we don't need to update anything no matter what.
3. If the packet has an earlier sequence number than expected, it has type r_retransmit. This refers to data that has been duplicated in some way.
Note that these would not be FIN or RST packets, since they would close the connection, making the sender unable to send data again.
4. If the packet type is FIN or RST, it has effect r_fin or r_rst, respectively
5. Otherwise, the packet is data and has type r_data
6. r_ignore only results from an ill-formed or problematic packet
*/

fixpoint tcp_reorder_effect get_reorder_effect(tcp_type ty, int plen, int seq, int exp_seq) {
	return 
	(ty == syn ? r_syn :
	(ty == ack && plen == 0 ? r_ack :
	(cmp(exp_seq, seq) > 0 ? r_retransmit : 
	(ty == fin ? r_fin :
	(ty == rst ? r_rst : r_data)))));
}

/* Next, we need to describe how the expected sequence number should be updated with each event. The semantics, based on RFC-793 and the definition of the expected
sequence number, are as follows:
1. If seq (the current sequence number) > exp_seq, there is a gap, and we should not update anything; we cannot process more bytes in order.
1. A SYN packet (r_syn) or FIN packet (f_fin) increases the sequence number by 1 (data is ignored).
2. An RST data does not affect the expected sequence number, since it closes the connection and no more data will be receieved.
3. Suppose the expected sequence number is exp_seq, and the packet has effect r_retransmit with sequence number seq and length plen. Because of the effect (and since 
	the expected sequence number is strictly increasing) exp_seq > seq. If seq + plen < exp_seq, we do not change the expected sequence (still, the same number of 
	bytes are complete). Otherwise, update exp_seq to seq + plen, since now all bytes before have been processed.
4. Otherwise (r_ack or r_data), updated exp_seq to be seq + plen. For an r_ack, plen = 0, so there is no change (which is correct; ACK packets do not change sequence numbers).
	We know that seq <= exp_seq, so it is safe to update exp_seq to be seq+plen (all bytes will have been processed). */
	
fixpoint int update_exp_seq(tcp_reorder_effect ev, int plen, int seq, int exp_seq) {
	return
	(cmp(seq, exp_seq) > 0 || ev == r_rst ? exp_seq :
	(ev == r_syn || ev == r_fin ? exp_seq + 1 :
	(ev == r_retransmit ? (cmp(seq + plen, exp_seq) > 0 ? seq + plen : exp_seq) :
	seq + plen)));
}
@*/


#endif
