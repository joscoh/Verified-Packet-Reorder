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
//@ requires true;
//@ ensures result == 0 ? true : tcp_packet_list_tp(result, nil, 0, 0);
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
	//@close tcp_packet_list_tp(ord, nil, 0, 0);

	return ord;
}

/* Destroys a TCP reorderer, freeing any resources it may be using
 *
 * Parameters:
 * 	ord - the reorderer to be destroyed
 */
void tcp_destroy_reorderer(tcp_packet_list_t *ord)
//@ requires tcp_packet_list_tp(ord, ?seqs, ?start, ?end);
//@ ensures true;
{
	//@open tcp_packet_list_tp(ord, seqs, start, end);
	tcp_packet_t *head = ord->list;
	tcp_packet_t *tmp;
	
	/* Free any packets we may still be hanging onto */
	while (head != NULL)
	//@invariant ord->destroy_packet |-> _ &*& head == 0 ? true : tcp_packet_full(head, end, _, _);
	   {
	   //@open tcp_packet_full(head, end, _, _);
	   //@open tcp_packet_partial(head, end, _, _, _);
	   //@open tcp_packet_single(head, _);
	   ///@open tcp_packet_partial_aux(head, end, _, _);
		if (ord->destroy_packet)
			//TODO: Verifast has problems with this - might need pre/post conditions
			//(*(ord->destroy_packet))(head->data);
			free(head->data);
		else
			free(head->data);
		tmp = head;
		head = head->next;
		tmp->next = NULL;
		free(tmp);
		/*@
		if(head != 0) {
			//close tcp_packet_partial(head, end, _, _, _);
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
 //JOSH - changed to int to reflect error state - malloc not working
static int insert_packet(tcp_packet_list_t *ord, void *packet, 
		uint32_t seq, uint32_t plen, double ts, tcp_reorder_t type)
//@requires tcp_packet_list_tp(ord, ?l, ?start, ?end) &*& malloc_block(packet, plen) &*& chars(packet, plen, _) &*& inrange(seq) == true &*& !mem(seq, l);
/*@ ensures result == 0 ? 
	tcp_packet_list_tp(ord, l, start, end) &*& malloc_block(packet, plen) &*& chars(packet, plen, _) 
	: tcp_packet_list_tp(ord, insert(seq, l), ?start1, ?end1); @*/
{

	tcp_packet_t *tpkt = (tcp_packet_t *)malloc(sizeof(tcp_packet_t));
	//JOSH - added
	if(tpkt == 0) return 0;
	tcp_packet_t *it = NULL;
	tcp_packet_t *prev = NULL;

	tpkt->type = type;
	tpkt->seq = seq;
	tpkt->plen = plen;
	tpkt->data = packet;
	tpkt->ts = ts;
	
	//@close tcp_packet_single(tpkt, seq);
	
	//@open tcp_packet_list_tp(ord, l, start, end);

	/* If we're the first thing to go into the list, this is pretty easy */
	if (ord->list == NULL) {
		//@ assert(l==nil);
		tpkt->next = NULL;
		ord->list = tpkt;
		ord->list_end = tpkt;
		ord->list_len += 1;
		///@close tcp_packet_partial_aux(tpkt, tpkt, insert(seq, nil), _);
		///@close tcp_packet_single(tpkt, _);
		//@close tcp_packet_partial(tpkt, tpkt, 0, insert(seq, nil), _);
		//@close tcp_packet_full(tpkt, tpkt, insert(seq, nil), _);
		//@close tcp_packet_list_tp(ord, insert(seq, nil), tpkt, tpkt);
		return 1;
	}
	

	/* A lot of inserts should be at the end of the list */
	it = ord->list_end;
	//@open tcp_packet_full(start, end, l, ?start_seq);
	///@full_end_nonnull(start, end);
	assert(it != NULL);
	
	//For this part, we need to reason about the end rather than the beginning of the list
	//First, we need to get the start seq
	//@partial_start_implies_end(start, end, 0, l, start_seq);
	//Get end_seq in context
	//@open tcp_packet_partial_end(start, end, 0, l, start_seq, ?end_seq);
	//@open tcp_packet_single(end, end_seq);
	if (seq_cmp(seq, it->seq) >= 0) {
		tpkt->next = NULL;
		it->next = tpkt;

		ord->list_end = tpkt;
		ord->list_len += 1;
		
		//@close tcp_packet_partial_end(tpkt, tpkt, 0, cons(seq, nil), seq, seq);
		//@close tcp_packet_single(end, end_seq);
		//@close tcp_packet_partial_end(start, end, tpkt, l, start_seq, end_seq);
		//need to prove sorted
		//@partial_end_contents_forall_inrange(start, end, tpkt, l, start_seq, end_seq); //everything in l is in range
		//@partial_end_contents_ub(start, end, tpkt, l, start_seq, end_seq); // everything in l is <= end_seq
		//@insert_end(l, end_seq, seq); // since seq is larger, insert seq l == l ++ [seq]
		//@insert_sorted(seq, l); //and this is sorted
		//@partial_app(start, end, tpkt, tpkt, 0, l, cons(seq, nil), start_seq, seq, end_seq, seq);
		//@partial_end_implies_start(start, tpkt, 0, insert(seq, l), start_seq, seq);
		//@close tcp_packet_full(start, tpkt, insert(seq, l), _);
		//@close tcp_packet_list_tp(ord, insert(seq, l), start, tpkt);		
		return 1;
	}
	
	//@ assume(false);

	/* Otherwise, find the appropriate spot for the packet in the list */
	for (it = ord->list; it != NULL; it = it->next) {
		if (seq_cmp(it->seq, seq) > 0) {
			tpkt->next = it;
			if (prev)
				prev->next = tpkt;
			else
				ord->list = tpkt;
			ord->list_len += 1;
			return 1;
		}
		prev = it;
	}

	assert(it != NULL);
	
	//NOTE: this is just insert, so here is plan:
	// have our structure
	//need notion that a packet is "in" the structure - show equiv to : we can split in two on this packet into partial
	// keep track of it and prev - have that prev.seq <= it.seq and partial(start, prev), partial(it, end) 
	//with next pointers appropriate (may need to change predicates or have partial(prev, end) or something or split into start -> a -> b -> end (better)
	// invariant is that seq < it.seq 
	//todo; verify insertion in dafny and see what invariant should be

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
{
	libtrace_ip_t *ip;
	libtrace_tcp_t *tcp; 
	void *packet_data;
	uint32_t seq;
	uint32_t plen;
	double pkt_ts;
	tcp_reorder_t type;

	ip = trace_get_ip(packet);
	tcp = trace_get_tcp(packet);

	/* Non-TCP packets cannot be reordered */
	if (tcp == NULL)
		return TCP_REORDER_IGNORE;

	seq = ntohl(tcp->seq);
	plen = (htons(ip->ip_len) - (ip->ip_hl * 4) - (tcp->doff * 4));
	pkt_ts = trace_get_seconds(packet);

	/* Pass the packet off to the read callback to extract the appropriate
	 * packet data */
	packet_data = ord->read_packet(ord->expected_seq, packet);
	
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

	else if (seq_cmp(ord->expected_seq, seq) > 0)
		type = TCP_REORDER_RETRANSMIT;
	
	else if (tcp->fin)
		type = TCP_REORDER_FIN;
	
	else if (tcp->rst)
		type = TCP_REORDER_RST;
	
	else
		type = TCP_REORDER_DATA;
	

	/* Now actually push it on to the list */
	insert_packet(ord, packet_data, seq, plen, pkt_ts, type);
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
tcp_packet_t *tcp_pop_packet(tcp_packet_list_t *ord) {

	tcp_packet_t *head = ord->list;

	/* No packets remaining in the list */
	if (head == NULL)
		return NULL;

	if (seq_cmp(head->seq, ord->expected_seq) > 0) {
		/* Not the packet we're looking for - sequence number gap */
		return NULL;
	}

	/* Remove the packet from the list */
	if (ord->list_end == head)
		ord->list_end = NULL;
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

		if (seq_cmp(head->seq + head->plen, ord->expected_seq) > 0) 
			ord->expected_seq = head->seq + head->plen;
	}

	return head;
	
}

