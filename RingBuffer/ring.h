#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP_LIMIT 1048576

struct ring;

struct ring* ring_create(int capacity);

bool ring_full(struct ring* r);

bool ring_empty(struct ring* r);

void ring_push_back(struct ring* r,
                    struct packet* p);

void ring_pop_front(struct ring* r,
                    struct packet* p);

#endif//_RING_H_INCLUDED_
