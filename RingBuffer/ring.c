#include <stdlib.h>
#include "ring.h"

struct ring {
  struct packet *array;
  int cap;
  int begin;
  int len;
};

// Describe a ring buffer - we use 2 lists for the front (next to be removed) and back (next to be added)
/*@
  
  //First we describe a packet array with contents l (TODO: may need to involve lengths)
  predicate arr_list(struct packet *arr, list<int> l) =
    switch(l) {
      case nil : return true;
      case cons(h, t) : return packet_pred(arr, h) &*& arr_list(arr+1, t);
   };
   
   predicate empty_arr(struct packet *arr, int length) =
   //TODO: bounds info
   chars((void*)arr, length * sizeof(struct packet), _);
   
   
   predicate ring_vals(struct ring *ring, struct packet *arr, int cap, int beg, int len) =
     ring->len |-> len &*& ring->cap |-> cap &*& ring->array |-> arr 
      &*& ring->begin |-> beg;
  	

   predicate ring_contents(struct ring *ring, list<int> front, list<int> back) =
      malloc_block_ring(ring) &*& ring_vals(ring, ?arr, ?cap, ?beg, ?len) &*&
      malloc_block_chars((void*)arr, cap * sizeof(struct packet)) &*&
      len == length(front) + length(back) &*& len <= cap &*&
      arr_list(arr, back) &*& arr_list(arr + beg, front) &*& empty_arr(arr + (beg - cap - , cap - len);
 @*/
     

struct ring* ring_create(int capacity)
//@ requires 0 <= capacity &*& 0 <= (capacity * sizeof(struct packet));
//@ ensures result == 0 ? true : ring_contents(result, nil, nil);
{
  struct ring* ret = malloc(sizeof(struct ring));
  if (ret == 0) {
   return 0;
  }
  struct packet* arr = malloc(sizeof (struct packet)*capacity);
  if (arr == 0) {
    free(ret);
    return 0;
  }
  ret->array = arr;
  ret->begin = 0;
  ret->len = 0;
  ret->cap = capacity;
  //@close arr_list(arr, nil);
  //@close arr_list((arr + (sizeof(struct packet) * 0)), nil);
  //@close ring_vals(ret, arr, capacity, 0, 0);
  //@close ring_contents(ret, nil, nil);
  return ret;
}

bool ring_full(struct ring* r)
{
  return r->len == r->cap;
}

bool ring_empty(struct ring* r)
{
  return r->len == 0;
}

void ring_push_back(struct ring* r, struct packet* p)
{
  int end = r->begin + r->len;
  if ( r->cap <= end ) {
    end = end - r->cap;
  } else {
  }
  struct packet* tgt_pkt = (struct packet*)r->array + end;
  tgt_pkt->port = p->port;
  r->len = r->len + 1;
}

void ring_pop_front(struct ring* r, struct packet* p)
{
  struct packet* src_pkt = (struct packet*)r->array + r->begin;
  p->port = src_pkt->port;
  r->len = r->len - 1;
  r->begin = r->begin + 1;
  if (r->cap <= r->begin) {
    r->begin = 0;
  } else {
  }
}
