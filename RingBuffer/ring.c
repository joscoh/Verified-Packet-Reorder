#include <stdlib.h>
#include "ring.h"

struct ring {
  struct packet *array;
  int cap;
  int begin;
  int len;
};

struct ring* ring_create(int capacity)
{
  struct ring* ret = malloc(sizeof(struct ring));
  if (ret == 0) return 0;
  struct packet* arr = malloc(sizeof (struct packet)*capacity);
  if (arr == 0) {
    free(ret);
    return 0;
  }
  ret->array = arr;
  ret->begin = 0;
  ret->len = 0;
  ret->cap = capacity;
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
