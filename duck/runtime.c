// Duck low-level runtime system

#include "runtime.h"
#include <gc/gc.h>
#include <stdio.h>
#include <stdlib.h>

// Unfortunately, the Boehm GC doesn't seem to like the Haskell runtime,
// which causes values to be incorrectly freed.  Once this is fixed,
// the folowing line should be uncommented.
// #define USE_BOEHM

void duck_runtime_init()
{
#ifdef USE_BOEHM
	GC_INIT();
#endif
}

value duck_malloc(size_t n)
{
#ifdef USE_BOEHM
    return GC_MALLOC(n);
#else
    return malloc(n);
#endif
}

value duck_malloc_atomic(size_t n)
{
#ifdef USE_BOEHM
    return GC_MALLOC_ATOMIC(n);
#else
	return malloc(n);
#endif
}
