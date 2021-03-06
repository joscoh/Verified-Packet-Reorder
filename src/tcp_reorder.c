/*
 * This file is part of libflowmanager
 *
 * Copyright (c) 2009 The University of Waikato, Hamilton, New Zealand.
 * Author: Shane Alcock
 *          
 * All rights reserved.
 *
 * This code has been developed by the University of Waikato WAND 
 * research group. For further information please see http://www.wand.net.nz/
 *
 * libflowmanager is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * libflowmanager is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with libflowmanager; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * $Id$
 *
 */

/* Code to reorder TCP packets based on strict sequence number order, rather
 * than chronological order.
 *
 * API relies on the user to provide callback functions for extracting the data
 * they want from each packet before reordering is attempted. This is because
 * libtrace packets themselves are very large (memory-wise) so we cannot
 * realistically afford to simply copy every packet that we reorder.
 *
 * Instead, we ask that the user write their own function that extracts just
 * the information they need and we'll store that for them instead. If you
 * still want to copy the entire packet, you're more than welcome to do so
 * inside your own callback - just don't say I didn't warn you!
 *
 * A destroy callback is also required, which will be used whenever a packet
 * is destroyed outside of the caller's direct control, i.e. when a reorderer
 * is freed. This is to ensure that memory allocated during the read callback
 * can be freed rather than leaked.
 */

#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
//#include <libtrace.h>
#include <stdint.h>


//@ #include "sort.gh"
#include "tcp_reorder.h"

/* Compares two sequence numbers, dealing appropriate with wrapping.
 *
 * Parameters:
 * 	seq_a - the first sequence number to compare
 * 	seq_b - the second sequence number to compare
 *
 * Returns:
 * 	the result of subtracting seq_b from seq_a (seq_a - seq_b, in other
 * 	words), taking sequence number wraparound into account
 */
static int seq_cmp (uint32_t seq_a, uint32_t seq_b)
//@ requires seq_a <= UINT32_MAX &*& seq_b <= UINT32_MAX; //NOTE: AXIOM
//@ ensures result == cmp(seq_a, seq_b);
{
	//@assume(false);

        if (seq_a == seq_b) return 0;

        if (seq_a > seq_b)
                return (int)(seq_a - seq_b);
        else
                return (int)(UINT32_MAX - ((seq_b - seq_a) - 1));

}

/* Creates and returns a new TCP reorderer
 *
 * Parameters:
 * 	cb - a callback function to be called for each packet pushed onto the
 * 	     reorder
 * 	destroy_cb - a callback function to be called whenever a packet is
 * 		     removed from the reorderer
 *
 * Returns:
 * 	a pointer to a newly allocated TCP reorderer
 */
tcp_packet_list_t *tcp_create_reorderer(read_packet_callback *cb, destroy_packet_callback *destroy_cb)
//@ requires is_read_packet_callback(cb) == true &*& destroy_cb != 0 &*& is_destroy_packet_callback(destroy_cb) == true;
//@ ensures result == 0 ? true : tcp_packet_list_tp(result, nil, 0);
		//void *(*cb)(uint32_t, libtrace_packet_t *),
		//void (*destroy_cb)(void *))
		 {
	tcp_packet_list_t *ord = 
		(tcp_packet_list_t *)malloc(sizeof(tcp_packet_list_t));
	if(ord == 0) return 0;
	
	ord->expected_seq = 0;
	ord->list = NULL;
	ord->list_end = NULL;
	ord->read_packet = cb;
	ord->destroy_packet = destroy_cb;
	ord->list_len = 0;
	//@close tcp_packet_list_wf(ord, 0, 0, 0);
	//@close tcp_packet_list_tp(ord, nil,0);

	return ord;
}

/* Destroys a TCP reorderer, freeing any resources it may be using
 *
 * Parameters:
 * 	ord - the reorderer to be destroyed
 */
 //NOTE: This function is unsafe: if ord->destroy_packet is zero, it free's data that may not have been malloc'ed. To avoid this,
 //we assume that ord->destroy_packet is nonzero
void tcp_destroy_reorderer(tcp_packet_list_t *ord)
//@ requires tcp_packet_list_tp(ord, ?seqs, ?exp_seq);
//@ ensures true;
{
	//@open tcp_packet_list_tp(ord, seqs, exp_seq);
	//@open tcp_packet_list_wf(ord, ?end, _, exp_seq);
	tcp_packet_t *head = ord->list;
	tcp_packet_t *tmp;
	
	/* Free any packets we may still be hanging onto */
	while (head != NULL)
	//@invariant ord->destroy_packet |-> ?d &*& d != 0 &*& is_destroy_packet_callback(d) == true &*& head == 0 ? true : tcp_packet_full(head, end, _, _);
	   {
	   //@open tcp_packet_full(head, end, _, _);
	   //@open tcp_packet_partial(head, end, _, _, _, _);
	   //@open tcp_packet_single(head, _, _, _);
		if (ord->destroy_packet) {
			//Need to do in 2 parts for Verifast
			destroy_packet_callback *des = (ord->destroy_packet);
			des(head->data);
			//(*(ord->destroy_packet))(head->data);
			}
		else
			//NOTE - unreachable by assumption
			free(head->data);
		tmp = head;
		head = head->next;
		tmp->next = NULL;
		free(tmp);
		/*@
		if(head != 0) {
			close tcp_packet_full(head, end, _, _);
		}
		@*/
	}

	free(ord);

}

/* Inserts packet data into a reorderer
 *
 * Parameters:
 * 	ord - the reorderer to insert the packet into
 * 	packet - packet data that has been extracted using a read callback
 * 	seq - the sequence number of the packet
 * 	plen - the payload length of the packet
 * 	ts - the timestamp of the packet
 * 	type - the packet type, e.g. SYN, FIN, RST, retransmit
 */
 //NOTE - changed to int to reflect error state - malloc not working
static int insert_packet(tcp_packet_list_t *ord, void *packet, 
		uint32_t seq, uint32_t plen, double ts, tcp_reorder_t type)
//@requires tcp_packet_list_tp(ord, ?l, ?exp_seq) &*& data_present(packet) &*& inrange(seq) == true &*& valid_reorder_t(type) == true;
/*@ ensures result == 0 ? 
	tcp_packet_list_tp(ord, l, exp_seq) &*& data_present(packet)
	: tcp_packet_list_tp(ord, insert(seq, reorder_t_to_effect(type), l), exp_seq); @*/
{

	tcp_packet_t *tpkt = (tcp_packet_t *)malloc(sizeof(tcp_packet_t));
	//NOTE - added
	if(tpkt == 0) return 0;
	tcp_packet_t *it = NULL;
	tcp_packet_t *prev = NULL;

	tpkt->type = type;
	tpkt->seq = seq;
	tpkt->plen = plen;
	tpkt->data = packet;
	tpkt->ts = ts;
	
	//@tcp_reorder_effect eff = reorder_t_to_effect(type);
	//@ reorder_t_effect_inv(type);
	//@close tcp_packet_single(tpkt, seq, eff, plen);
	
	//@open tcp_packet_list_tp(ord, l, exp_seq);
	//@open tcp_packet_list_wf(ord, ?end, length(l), exp_seq);

	/* If we're the first thing to go into the list, this is pretty easy */
	if (ord->list == NULL) {
		tpkt->next = NULL;
		ord->list = tpkt;
		ord->list_end = tpkt;
		ord->list_len += 1;
		//@close tcp_packet_partial(tpkt, tpkt, 0, insert(seq, eff, nil), _, _);
		//@close tcp_packet_full(tpkt, tpkt, insert(seq, eff, nil), _);
		//@close tcp_packet_list_wf(ord, tpkt, 1, exp_seq); 
		//@close tcp_packet_list_tp(ord, insert(seq, eff, nil), exp_seq);
		return 1;
	}
	

	/* A lot of inserts should be at the end of the list */
	it = ord->list_end;
	//@ tcp_packet_t *start = ord->list;
	//@open tcp_packet_full(start, end, l, ?start_seq);
	//Get start_eff in context
	//@open tcp_packet_partial(start, end, 0, l, start_seq, ?start_eff);
	//@close tcp_packet_partial(start, end, 0, l, start_seq, start_eff);
	assert(it != NULL);
	
	//For this part, we need to reason about the end rather than the beginning of the list
	//First, we need to get the start seq
	//@partial_start_implies_end(start, end, 0, l, start_seq, start_eff);
	//Get end_seq in context
	//@open tcp_packet_partial_end(start, end, 0, l, start_seq, start_eff, ?end_seq, ?end_eff);
	//@open tcp_packet_single(end, end_seq, end_eff, ?end_plen);
	if (seq_cmp(seq, it->seq) >= 0) {
		tpkt->next = NULL;
		it->next = tpkt;

		ord->list_end = tpkt;
		ord->list_len += 1;
		
		//@close tcp_packet_partial_end(tpkt, tpkt, 0, cons(pair(seq, eff), nil), seq, eff, seq, eff);
		//@close tcp_packet_single(end, end_seq, end_eff, end_plen);
		//@close tcp_packet_partial_end(start, end, tpkt, l, start_seq, start_eff, end_seq, end_eff);
		//need to prove sorted
		//@partial_end_contents_forall_inrange(start, end, tpkt, l, start_seq, start_eff, end_seq, end_eff); //everything in l is in range
		//@partial_end_contents_ub(start, end, tpkt, l, start_seq, start_eff, end_seq, end_eff); // everything in l is <= end_seq
		//@insert_end(l, end_seq, seq, eff); // since seq is larger, insert seq l == l ++ [seq]
		//@insert_sorted(seq, eff, l); //and this is sorted
		//@partial_app(start, end, tpkt, tpkt, 0, l, cons(pair(seq, eff), nil), start_seq, start_eff, seq, eff, end_seq, end_eff, seq, eff);
		//@partial_end_implies_start(start, tpkt, 0, insert(seq, eff, l), start_seq, start_eff, seq, eff);
		//@close tcp_packet_full(start, tpkt, insert(seq, eff, l), _);
		//@close tcp_packet_list_wf(ord, tpkt, 1 + length(l), exp_seq);
		//@close tcp_packet_list_tp(ord, insert(seq, eff, l),  exp_seq);		
		return 1;
	}
	
	/* Otherwise, find the appropriate spot for the packet in the list */
	
	//Establish invariants
	//@close tcp_packet_single(end, end_seq, end_eff, end_plen);
	//@close tcp_packet_partial_end(start, end, 0, l, start_seq, start_eff, end_seq, end_eff);
	//@close tcp_packet_list_wf(ord, end, length(l), exp_seq);
	
	//It will also be helpful to know that seq != end_seq
	//@partial_end_contents_mem(start, end, 0, l, start_seq, start_eff, end_seq, end_eff);
	
	//@close tcp_packet_partial_end_gen(start, prev, start, nil, start_seq, start_eff, 0, end_eff); //end_eff can be anything here
	//@close tcp_packet_partial_end_gen(start, end, 0, l, start_seq, start_eff, end_seq, end_eff);
	
	//NOTE - changed from for loop to while loop - this is much easier invariant-wise (because we don't need to have it->next accessible when the loop continues which is
	//a huge pain.
	it = ord->list;
	while(it!= NULL)
	/*@
	 invariant tcp_packet_single(tpkt, seq, eff, plen) &*& tpkt->next |-> _ &*& tcp_packet_list_wf(ord, end, length(l), exp_seq) &*& ord->list |-> start &*&
	 	tcp_packet_partial_end_gen(start, prev, it, ?l1, start_seq, start_eff, ?prev_seq, ?prev_eff) &*& 
	 	tcp_packet_partial_end_gen(it, end, 0, ?l2, ?it_seq, ?it_eff, end_seq, end_eff) &*&
	 	append(l1, l2) == l &*& 
		prev == 0 && it != 0 ? start == it && it_seq == start_seq && it_eff == start_eff
		 : it == 0 ? prev == end && prev_seq == end_seq && prev_eff == end_eff && cmp(end_seq, seq) < 0
		 : cmp(prev_seq, seq) <= 0; @*/
	// This invariant is quite complicated. The first case is the start, the second is the (trivial) end, and the third case is interesting. It says we can split up l into
	// l1 and l2, where seq is larger than the largest value in l1 (so we should insert in l2)
	      {
	      //Get l1 and l2 in context (this is why we need the gen version of the partial_end predicate
	      //@ open tcp_packet_partial_end_gen(start, prev, it, l1, start_seq, start_eff, prev_seq, prev_eff);
	      //@ open tcp_packet_partial_end_gen(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
	      /*@ 
	      	// open things for each case so we can access it->seq
	      	if(prev == 0 && it != 0) {
	      		if(it == end) {
	      			open tcp_packet_partial_end(it, end, 0, l2, start_seq, start_eff, end_seq, end_eff);
	      		}
	      		else {
	      			tcp_partial_packet_end_ind(it, end, 0, l2, start_seq, start_eff, end_seq, end_eff);
	      		}
	      		open tcp_packet_single(it, start_seq, start_eff, ?start_plen);
	      	}
	      	else if(it == 0) {} //trivial
	      	else {
	      		open tcp_packet_partial_end(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
	      		if(it != end) {
	      			close tcp_packet_partial_end(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
	      			tcp_partial_packet_end_ind(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
	      		}
	      		open tcp_packet_single(it, it_seq, it_eff, ?it_plen);
	      		// In this case, we also need to be able to access prev->next
	      		open tcp_packet_partial_end(start, prev, it, l1, start_seq, start_eff, prev_seq, prev_eff);
	      		open tcp_packet_single(prev, prev_seq, prev_eff, ?prev_plen);
	      	}
	      	@*/
	      	// this was the goal - now we can access it->seq
	      	//@ open tcp_packet_single(tpkt, seq, eff, plen);
	      	//@ open tcp_packet_list_wf(ord, end, length(l), exp_seq);
	      	
		if (seq_cmp(it->seq, seq) > 0) {
			tpkt->next = it;
			if (prev)
				prev->next = tpkt;
			else
				ord->list = tpkt;
			ord->list_len += 1;
			// Establish postconditions here
			//@ close tcp_packet_single(tpkt, seq, eff, plen);
			/*@
				if(prev) {
					// now we have start --> prev -> tkpt -> it --> end (the most interesting case)
					// First, we deal with start ---> tkpt
					close tcp_packet_single(it, it_seq, it_eff, it->plen);
					close tcp_packet_single(prev, prev_seq, prev_eff, prev->plen);
					
					close tcp_packet_partial_end(start, prev, tpkt, l1, start_seq, start_eff, prev_seq, prev_eff);
					//in either case, we need to close tcp_packet_partial_end(it, end, 0, l2, it_seq, end_seq)
					if(it == end) {
						close tcp_packet_partial_end(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
					}
					else {
						//get next and next_seq for fold lemma
						open tcp_packet_partial_end(?next, end, 0, tail(l2), ?next_seq, ?next_eff, end_seq, end_eff);
						close tcp_packet_partial_end(next, end, 0, tail(l2), next_seq, next_eff, end_seq, end_eff);
						tcp_partial_packet_end_fold(it, next, end, 0, l2, it_seq, it_eff, next_seq, next_eff, end_seq, end_eff);
					}
					//Now we deal with tkpt --> end
					close tcp_packet_partial_end(tpkt, tpkt, it, cons(pair(seq, eff), nil), seq, eff, seq, eff);
					partial_end_contents_forall_inrange(it, end, 0, l2, it_seq, it_eff, end_seq, end_eff);
					partial_app(tpkt, tpkt, it, end, 0, cons(pair(seq, eff), nil), l2, seq, eff, it_seq, it_eff, seq, eff, end_seq, end_eff);
					//Now we can combine everything and get start ---> end
					//prove sorted
					partial_end_contents_forall_inrange(start, prev, tpkt, l1, start_seq, start_eff, prev_seq, prev_eff);
					partial_end_contents_ub(start, prev, tpkt, l1, start_seq, start_eff, prev_seq, prev_eff);
					insert_app(l1, l2, prev_seq, seq, eff);
					forall_append(map(fst,l1), map(fst,l2), inrange);
					map_append(fst, l1, l2);
					insert_sorted(seq, eff, append(l1, l2));
					
					//Now we can combine everything and prove the postcondition
					partial_app(start, prev, tpkt, end, 0, l1, insert(seq, eff, l2), start_seq, start_eff, seq, eff, prev_seq, prev_eff, end_seq, end_eff);
					partial_end_implies_start(start, end, 0, insert(seq, eff, l), start_seq, start_eff, end_seq, end_eff);
					close tcp_packet_full(start, end, insert(seq, eff, l), start_seq);
					close tcp_packet_list_wf(ord, end, length(insert(seq, eff, l)), exp_seq);
					close tcp_packet_list_tp(ord, insert(seq, eff, l), exp_seq);
				}
				else {
					// In each case, we need to show that we have tcp_partial_end(tpkt, end, 0, insert(seq, l), seq, _, end_seq);
					if(it == end) {
						close tcp_packet_single(it, end_seq, end_eff, end->plen);
						close tcp_packet_partial_end(it, end, 0, l, end_seq, end_eff, end_seq, end_eff);
						tcp_partial_packet_end_fold(tpkt, it, end, 0, insert(seq, eff, l), seq, eff, end_seq, end_eff, end_seq, end_eff);
					}
					else {
						close tcp_packet_single(it, start_seq, start_eff, start->plen);
						//get seq1
						open tcp_packet_partial_end(?next, end, 0, tail(l), ?seq1, ?eff1, end_seq, end_eff);
						close tcp_packet_partial_end(next, end, 0, tail(l), seq1, eff1, end_seq, end_eff);
						tcp_partial_packet_end_fold(it, next, end, 0, l, start_seq, start_eff, seq1, eff1, end_seq, end_eff);
						tcp_partial_packet_end_fold(tpkt, it, end, 0, insert(seq, eff, l), seq, eff, start_seq, start_eff, end_seq, end_eff);
					}
					// In both cases, close all remaining predicates
					partial_end_implies_start(tpkt, end, 0, insert(seq, eff, l), seq, eff, end_seq, end_eff);
					close tcp_packet_full(tpkt, end, insert(seq, eff, l), seq);
					close tcp_packet_list_wf(ord, end, length(insert(seq, eff, l)), exp_seq);
					close tcp_packet_list_tp(ord, insert(seq, eff, l), exp_seq);
				}
			@*/	
		
			return 1;
		}
		//@tcp_packet_t *old_prev = prev;
		//@tcp_packet_t *old_it = it;
		//@tcp_packet_t *new_prev = it;
		//@tcp_packet_t *new_it = it->next;
		prev = it;
		it = it->next;
		//Preservation of loop invariant
		//@close tcp_packet_single(tpkt, seq, eff, plen);
		//@close tcp_packet_list_wf(ord, end, length(l), exp_seq);
		//prove cmp(end_seq, seq) < 0
		/*@
			if(cmp(end_seq, seq) == 0) { 
				cmp_inj(end_seq, seq);
			}
		@*/
		//prove cmp(it_seq, seq) < 0
		/*@
			if(cmp(it_seq, seq) == 0) {
				cmp_inj(it_seq, seq);
			}
		@*/
		//prove that the heap invariants are preserved
		/*@
			if(old_prev) {
				//First part is start --> prev -> it, and it becomes the new prev
				close tcp_packet_single(old_prev, prev_seq, prev_eff, old_prev->plen);
				close tcp_packet_partial_end(start, old_prev, new_prev, l1, start_seq, start_eff, prev_seq, prev_eff);
				close tcp_packet_single(old_it, it_seq, it_eff, old_it->plen);
				close tcp_packet_partial_end(new_prev, new_prev, new_it, cons(pair(it_seq, it_eff), nil), it_seq, it_eff, it_seq, it_eff);
				//prove that l1 ++ [it_seq] is sorted - we know this because l = l1 ++ (it_seq :: l2) = (l1 ++ [it_seq]) ++ l2
				append_assoc(l1, cons(pair(it_seq, it_eff), nil), tail(l2));
				sorted_app1(append(l1, cons(pair(it_seq, it_eff), nil)), tail(l2));
				partial_app(start, old_prev, new_prev, new_prev, new_it, l1, cons(pair(it_seq, it_eff), nil), start_seq, start_eff, it_seq, it_eff, prev_seq, prev_eff, it_seq, it_eff); 
				close tcp_packet_partial_end_gen(start, new_prev, new_it, append(l1, cons(pair(it_seq, it_eff), nil)), start_seq, start_eff, it_seq, it_eff);
				if(old_it == end) {
					//We have start --> prev -> it = end, which becomes start --> prev' = it = = end, it' = null
					close tcp_packet_partial_end_gen(new_it, end, 0, nil, it_seq, it_eff, end_seq, end_eff);
				}
				else {
					//We have start --> prev -> it -> next --> end, which becomes start --> prev' = it -> it' = next --> end
					//need seq1
					open tcp_packet_partial_end(new_it, end, 0, tail(l2), ?seq1, ?eff1, end_seq, end_eff);
					close tcp_packet_partial_end(new_it, end, 0, tail(l2), seq1, eff1, end_seq, end_eff);
					partial_end_start_nonzero(new_it, end, 0, tail(l2), seq1, eff1, end_seq, end_eff); //new_it != 0
					close tcp_packet_partial_end_gen(new_it, end, 0, tail(l2), seq1, eff1, end_seq, end_eff);
				}
			}
			else {
				if(old_it == end) {
					close tcp_packet_single(new_prev, it_seq, it_eff, end->plen);
					close tcp_packet_partial_end(new_prev, new_prev, new_it, cons(pair(it_seq, it_eff), nil), it_seq, it_eff, it_seq, it_eff);
					close tcp_packet_partial_end_gen(new_prev, new_prev, new_it, cons(pair(it_seq, it_eff), nil), it_seq, it_eff, it_seq, it_eff);
					close tcp_packet_partial_end_gen(new_it, end, 0, nil, 0, it_eff, end_seq, end_eff); //0 and it_eff don't matter
				}
				else {
					close tcp_packet_single(new_prev, it_seq, it_eff, old_it->plen);
					close tcp_packet_partial_end(new_prev, new_prev, new_it, cons(pair(it_seq, it_eff), nil), it_seq, it_eff, it_seq, it_eff);
					close tcp_packet_partial_end_gen(new_prev, new_prev, new_it, cons(pair(it_seq, it_eff), nil), it_seq, it_eff, it_seq, it_eff);
					//get next and seq1 in context
					open tcp_packet_partial_end(?next, end, 0, tail(l), ?seq1, ?eff1, end_seq, end_eff);
					close tcp_packet_partial_end(next, end, 0, tail(l), seq1, eff1, end_seq, end_eff);
					partial_end_start_nonzero(next, end, 0, tail(l), seq1, eff1, end_seq, end_eff); //need to know next!= 0
					close tcp_packet_partial_end_gen(next, end, 0, tail(l), seq1, eff1, end_seq, end_eff);
				}
			}
		@*/	
	}
	//contradiction here - (hence the assert false statement) because we know seq cannot be larger than everything
	//@ cmp_antisym2(end_seq, seq);
	
	assert(it != NULL);

}


/* Pushes a libtrace packet onto a TCP reorderer
 *
 * Parameters:
 * 	ord - the reorderer to push the packet onto
 * 	packet - the packet to push on
 *
 * Parameters:
 * 	the type of the packet - if TCP_REORDER_IGNORE, the packet was not
 * 	pushed on at all and should be ignored by the caller
 */
tcp_reorder_t tcp_reorder_packet(tcp_packet_list_t *ord, 
	libtrace_packet_t *packet)
//@ requires valid_packet(packet, ?seqnum, ?plength, ?ty) &*& tcp_packet_list_tp(ord, ?l, ?exp_seq) &*& inrange(seqnum) == true;
/*@ ensures valid_packet(packet, seqnum, plength, ty) &*&
	result == effect_to_reorder_t(r_ignore) ?
		(get_reorder_effect(ty, plength, seqnum, exp_seq) == r_syn
			 ? tcp_packet_list_tp(ord, l, seqnum) : tcp_packet_list_tp(ord, l, exp_seq)) :
	result == effect_to_reorder_t(get_reorder_effect(ty, plength, seqnum, exp_seq)) &*&
	result == effect_to_reorder_t(r_syn) ? tcp_packet_list_tp(ord, insert(seqnum, get_reorder_effect(ty, plength, seqnum, exp_seq), l), seqnum) :
		tcp_packet_list_tp(ord, insert(seqnum, get_reorder_effect(ty, plength, seqnum, exp_seq), l), exp_seq);
@*/
{
	libtrace_ip_t *ip;
	libtrace_tcp_t *tcp; 
	void *packet_data;
	uint32_t seq;
	uint32_t plen;
	double pkt_ts;
	tcp_reorder_t type;
	
	//@open valid_packet(packet, seqnum, plength, ty);

	ip = trace_get_ip(packet);
	tcp = trace_get_tcp(packet);

	/* Non-TCP packets cannot be reordered */
	if (tcp == NULL)
		return TCP_REORDER_IGNORE;
		
	//@open libtrace_tcp_p(packet, tcp, seqnum, ?tcp_head_len, ty);
	//@open libtrace_ip_p(packet, ip, ?ip_head_len, ?ip_len);
	//@open valid_ip_packet(packet, ip_head_len, ip_len);
	//@open valid_tcp_packet(packet, seqnum, tcp_head_len, ty);

	seq = ntohl(tcp->seq);
	//NOTE - need to insert casts to make Verifast happy (this won't overflow because of packet specs, but Verifast doesn't check that yet)
	plen = ((uint32_t) (htons(ip->ip_len)) - ((uint32_t) (ip->ip_hl * 4)) - ((uint32_t) (tcp->doff * 4)));
	//@uint16_t ip_len_0 = ip->ip_len;
	//@htons_ntohs(ip_len_0);
	//NOTE - no idea why they use htons here - should be ntohs since we want plen to be in host byte order. But for all real purposes (eg: Linux), htons and ntohs are the same function,
	//so this is OK. Even in the paper about libtrace, they use ntohs(ip->ip_len) in their example, so I think this is a mistake.
	pkt_ts = trace_get_seconds(packet);

	/* Pass the packet off to the read callback to extract the appropriate
	 * packet data */
	 //NOTE - Verifast doesn't like this in one line; we need to split it up
	//@open tcp_packet_list_tp(ord, l, exp_seq);
	//@open tcp_packet_list_wf(ord, ?end, length(l), exp_seq);
	read_packet_callback *rp = ord->read_packet;
	packet_data = rp(ord->expected_seq, packet);
	
	/* No packet data? Ignore */
	if (packet_data == NULL)
		return TCP_REORDER_IGNORE;
	
	/* Determine the packet type */
	if (tcp->syn) {
		type = TCP_REORDER_SYN;
		ord->expected_seq = seq;
	}

	else if (tcp->ack && !tcp->fin && plen == 0)
		
		type = TCP_REORDER_ACK;
		///@assert(ty == ack || ty == rst_ack);
	

	else if (seq_cmp(ord->expected_seq, seq) > 0)
		type = TCP_REORDER_RETRANSMIT;
	
	else if (tcp->fin)
		type = TCP_REORDER_FIN;
	
	else if (tcp->rst)
		type = TCP_REORDER_RST;
	
	else
		type = TCP_REORDER_DATA;
		
	/*@
	if(tcp->syn) {
		close tcp_packet_list_wf(ord, end, length(l), seq);
		close tcp_packet_list_tp(ord, l, seq);
	} 
	else {
		close tcp_packet_list_wf(ord, end, length(l), exp_seq);
		close tcp_packet_list_tp(ord, l, exp_seq);
	} 
	@*/
	

	/* Now actually push it on to the list */
	//NOTE - handle failure case
	int res = insert_packet(ord, packet_data, seq, plen, pkt_ts, type);
	if (res == 0) {
		type = TCP_REORDER_IGNORE;
		//@open tcp_packet_list_tp(ord, l, ?s);
		//@open tcp_packet_list_wf(ord, ?e, length(l), s);
		destroy_packet_callback *dp = ord->destroy_packet;
		dp(packet_data);
		//@close tcp_packet_list_wf(ord, e, length(l), s);
		//@close tcp_packet_list_tp(ord, l, s);
	}
	//@ close valid_ip_packet(packet, ip_head_len, ip_len);
	//@ close valid_tcp_packet(packet, seqnum, tcp_head_len, ty);
	//@ close valid_packet(packet, seqnum, plength, ty);
	return type;

}


/* Pops the first reordered TCP packet off the reorderer's packet list. 
 *
 * Packets are only popped if they match the current expected sequence number.
 *
 * Parameters:
 * 	ord - the reorderer to pop a packet from
 *
 * Returns:
 * 	a pointer to the TCP packet that matches the expected sequence number.
 * 	If no such packet is currently in the reordering list, NULL is 
 * 	returned.
 *
 */
tcp_packet_t *tcp_pop_packet(tcp_packet_list_t *ord)
//@requires tcp_packet_list_tp(ord, ?l, ?exp_seq);
/*@ensures l == nil ? result == 0 &*& tcp_packet_list_tp(ord, l, exp_seq) :
	l == cons(pair(?seq, ?eff), ?tl) &*&
	(cmp(seq, exp_seq) > 0) ? result == 0 &*& tcp_packet_list_tp(ord, l, exp_seq) :
		tcp_packet_single(?start, seq, eff, ?plen) &*& start->next |-> _ &*& result == start &*&
		tcp_packet_list_tp(ord, tl, update_exp_seq(eff, plen, seq, exp_seq));
@*/
 
   {
	//@open tcp_packet_list_tp(ord, l, exp_seq);
	tcp_packet_t *head = ord->list;

	/* No packets remaining in the list */
	if (head == NULL) {
		return NULL;
		//@close tcp_packet_list_tp(ord, l, exp_seq);
	}
	//@open tcp_packet_full(?start, ?end, l, ?start_seq);
	//@open tcp_packet_partial(start, end, 0, l, start_seq, ?start_eff);
	//@open tcp_packet_single(start, start_seq, start_eff, ?start_plen);
	//@open tcp_packet_list_wf(ord, end, length(l), exp_seq);
	if (seq_cmp(head->seq, ord->expected_seq) > 0) {
		/* Not the packet we're looking for - sequence number gap */
		return NULL;
		//@close tcp_packet_list_wf(ord, end, length(l), exp_seq);
		//@close tcp_packet_single(start, start_seq, start_eff, start_plen);
		//@close tcp_packet_partial(start, end, 0, l, start_seq, start_eff);
		//@close tcp_packet_full(start, end, l, start_seq);
		//@close tcp_packet_list_tp(ord, l, exp_seq);
	}

	/* Remove the packet from the list */
	if (ord->list_end == head)
		ord->list_end = NULL;
	//@tcp_packet_t *next = head->next;
	ord->list = head->next;
	ord->list_len -= 1;
	

	/* Update the expected sequence number */
	if (head->type == TCP_REORDER_SYN)
		ord->expected_seq += 1;
	if (head->type == TCP_REORDER_FIN)
		ord->expected_seq += 1;
	if (head->type == TCP_REORDER_DATA) 
		ord->expected_seq = head->seq + head->plen;
	if (head->type == TCP_REORDER_RETRANSMIT) {
		//@assume(inrange(head->seq + head->plen) == true); //ASSUMPTION
		if (seq_cmp(head->seq + head->plen, ord->expected_seq) > 0) 
			ord->expected_seq = head->seq + head->plen;
	}
	//@effect_reorder_t_inv(start_eff);
	//@close tcp_packet_single(start, start_seq, start_eff, start_plen);
	//@update_exp_seq_inrange(start_eff, start_plen, start_seq, exp_seq); //NOTE: THIS IS AN ASSUMPTION
	/*@
		if(next) {
			//Get next_seq and next_eff
			open tcp_packet_partial(next, end, 0, tail(l), ?next_seq, ?next_eff);
			close tcp_packet_partial(next, end, 0, tail(l), next_seq, next_eff);
			close tcp_packet_full(next, end, tail(l), next_seq);
			close tcp_packet_list_wf(ord, end, length(l) - 1, update_exp_seq(start_eff, start_plen, start_seq, exp_seq));
			
		}
		else close tcp_packet_list_wf(ord, 0, length(l) - 1, update_exp_seq(start_eff, start_plen, start_seq, exp_seq));	
	@*/
	
	//@close tcp_packet_list_tp(ord, tail(l), update_exp_seq(start_eff, start_plen, start_seq, exp_seq));
	return head;
	
}

