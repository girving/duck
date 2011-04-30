// Duck low-level runtime system

#ifndef __DUCK_RUNTIME_H__
#define __DUCK_MALLOC_H__

#include <stddef.h>

struct _value;
typedef struct _value *value;

// Initialize the runtime system
extern void duck_runtime_init();

// Allocate a block of memory
extern value duck_malloc(size_t n);

// Allocate a guaranteed-pointer-free block of memory
extern value duck_malloc_atomic(size_t n);

#endif
