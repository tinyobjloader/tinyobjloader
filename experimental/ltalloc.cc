/*
Copyright (c) 2013, Alexander Tretyak
Copyright (c) 2015, r-lyeh
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

    * Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above
copyright notice, this list of conditions and the following disclaimer
in the documentation and/or other materials provided with the
distribution.
    * Neither the name of the author nor the names of its
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


  Note: The latest version of this memory allocator obtainable at
        http://ltalloc.googlecode.com/hg/ltalloc.cc

  Project URL: http://code.google.com/p/ltalloc
*/

#include "ltalloc.h"

#define LTALLOC_VERSION "2.0.0" /* (2015/06/16) - ltcalloc(), ltmsize(), ltrealloc(), ltmemalign(), LTALLOC_AUTO_GC_INTERVAL 
#define LTALLOC_VERSION "1.0.0" /* (2015/06/16) - standard STL allocator provided [see ltalloc.hpp file](ltalloc.hpp)
#define LTALLOC_VERSION "0.0.0" /* (2013/xx/xx) - fork from public repository */

//Customizable constants
//#define LTALLOC_DISABLE_OPERATOR_NEW_OVERRIDE
//#define LTALLOC_AUTO_GC_INTERVAL 3.0
#ifndef LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO
#define LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO 2//determines how accurately size classes are spaced (i.e. when = 0, allocation requests are rounded up to the nearest power of two (2^n), when = 1, rounded to 2^n, or (2^n)*1.5, when = 2, rounded to 2^n, (2^n)*1.25, (2^n)*1.5, or (2^n)*1.75, and so on); this parameter have direct influence on memory fragmentation - bigger values lead to reducing internal fragmentation (which can be approximately estimated as pow(0.5, VALUE)*100%), but at the same time increasing external fragmentation
#endif
#define CHUNK_SIZE     (64*1024)//size of chunk (basic allocation unit for all allocations of size <= MAX_BLOCK_SIZE); must be a power of two (as well as all following parameters), also should not be less than allocation granularity on Windows (which is always 64K by design of NT kernel)
#define CACHE_LINE_SIZE 64
#define MAX_NUM_OF_BLOCKS_IN_BATCH 256//maximum number of blocks to move between a thread cache and a central cache in one shot
static const unsigned int MAX_BATCH_SIZE = 64*1024;//maximum total size of blocks to move between a thread cache and a central cache in one shot (corresponds to half size of thread cache of each size class)
static const unsigned int MAX_BLOCK_SIZE = CHUNK_SIZE;//requesting memory of any size greater than this value will lead to direct call of system virtual memory allocation routine

//Platform-specific stuff

#ifdef __cplusplus
#define CPPCODE(code) code
#include <new>
#else
#define CPPCODE(code)
#endif

#ifdef LTALLOC_AUTO_GC_INTERVAL
#include <time.h>
#	if			LTALLOC_AUTO_GC_INTERVAL <= 0
#		undef	LTALLOC_AUTO_GC_INTERVAL 
#		define	LTALLOC_AUTO_GC_INTERVAL 3.00
#	endif
#endif

#ifdef __GNUC__

#define __STDC_LIMIT_MACROS
#include <stdint.h> //for SIZE_MAX
#include <limits.h> //for UINT_MAX
#define alignas(a) __attribute__((aligned(a)))
#define thread_local __thread
#define NOINLINE __attribute__((noinline))
#define CAS_LOCK(lock) __sync_lock_test_and_set(lock, 1)
#define SPINLOCK_RELEASE(lock) __sync_lock_release(lock)
#define PAUSE __asm__ __volatile__("pause" ::: "memory")
#define BSR(r, v) r = CODE3264(__builtin_clz(v) ^ 31, __builtin_clzll(v) ^ 63)//x ^ 31 = 31 - x, but gcc does not optimize 31 - __builtin_clz(x) to bsr(x), but generates 31 - (bsr(x) ^ 31)

#elif _MSC_VER

#define _ALLOW_KEYWORD_MACROS
#include <limits.h> //for SIZE_MAX and UINT_MAX
#define alignas(a) __declspec(align(a))
#define thread_local __declspec(thread)
#define NOINLINE __declspec(noinline)
#define CAS_LOCK(lock) _InterlockedExchange((long*)lock, 1)
#define SPINLOCK_RELEASE(lock) _InterlockedExchange((long*)lock, 0)
#define PAUSE _mm_pause()
#define BSR(r, v) CODE3264(_BitScanReverse, _BitScanReverse64)((unsigned long*)&r, v)
CPPCODE(extern "C") long _InterlockedExchange(long volatile *, long);
CPPCODE(extern "C") void _mm_pause();
#pragma warning(disable: 4127 4201 4324 4290)//"conditional expression is constant", "nonstandard extension used : nameless struct/union", and "structure was padded due to __declspec(align())"

#else
#error Unsupported compiler
#endif

#if __GNUC__ || __INTEL_COMPILER
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#else
#define likely(x) (x)
#define unlikely(x) (x)
#endif

static void SPINLOCK_ACQUIRE(volatile int *lock) {if (CAS_LOCK(lock)) while (*lock || CAS_LOCK(lock)) PAUSE;}

#include <assert.h>
#include <string.h> //for memset

#if SIZE_MAX == UINT_MAX
#define CODE3264(c32, c64) c32
#else
#define CODE3264(c32, c64) c64
#endif
typedef char CODE3264_check[sizeof(void*) == CODE3264(4, 8) ? 1 : -1];

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

#define VMALLOC(size) VirtualAlloc(NULL, size, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE)
#define VMFREE(p, size) VirtualFree(p, 0, MEM_RELEASE)

#else

#include <sys/mman.h>
#include <unistd.h>

#define VMALLOC(size) (void*)(((uintptr_t)mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0)+1)&~1)//with the conversion of MAP_FAILED to 0
#define VMFREE(p, size) munmap(p, size)

static size_t page_size()
{
	assert((uintptr_t)MAP_FAILED+1 == 0);//have to use dynamic check somewhere, because some gcc versions (e.g. 4.4.5) won't compile typedef char MAP_FAILED_value_static_check[(uintptr_t)MAP_FAILED+1 == 0 ? 1 : -1];
	static size_t pagesize = 0;
	if (!pagesize) pagesize = sysconf(_SC_PAGE_SIZE);//assuming that writing of size_t value is atomic, so this can be done safely in different simultaneously running threads
	return pagesize;
}

typedef struct PTrieNode            // Compressed radix tree (patricia trie) for storing sizes of system allocations
{                                   // This implementation have some specific properties:
    uintptr_t keys[2];              // 1. There are no separate leaf nodes (with both null children), as leaf's value is stored directly in place of corresponding child node pointer. Least significant bit of that pointer used to determine its meaning (i.e., is it a value, or child node pointer).
    struct PTrieNode *childNodes[2];// 2. Inserting a new element (key/value) into this tree require to create always an exactly one new node (and similarly for remove key/node operation).
} PTrieNode;                        // 3. Tree always contains just one node with null child (i.e. all but one nodes in any possible tree are always have two children).
#define PTRIE_NULL_NODE (PTrieNode*)(uintptr_t)1
static PTrieNode *ptrieRoot = PTRIE_NULL_NODE, *ptrieFreeNodesList = NULL, *ptrieNewAllocatedPage = NULL;
static volatile int ptrieLock = 0;

static uintptr_t ptrie_lookup(uintptr_t key)
{
	PTrieNode *node = ptrieRoot;
	uintptr_t *lastKey = NULL;
	while (!((uintptr_t)node & 1))
	{
		int branch = (key >> (node->keys[0] & 0xFF)) & 1;
		lastKey = &node->keys[branch];
		node = node->childNodes[branch];
	}
	assert(lastKey && (*lastKey & ~0xFF) == key);
	return (uintptr_t)node & ~1;
}

static void ptrie_insert(uintptr_t key, uintptr_t value, PTrieNode *newNode/* = (PTrieNode*)malloc(sizeof(PTrieNode))*/)
{
	PTrieNode **node = &ptrieRoot, *n;
	uintptr_t *prevKey = NULL, x, pkey;
	unsigned int index, b;
	assert(!((value & 1) | (key & 0xFF)));//check constraints for key/value
	for (;;)
	{
		n = *node;
		if (!((uintptr_t)n & 1))//not a leaf
		{
			int prefixEnd = n->keys[0] & 0xFF;
			x = key ^ n->keys[0];// & ~0xFF;
			if (!(x & (~(uintptr_t)1 << prefixEnd))) {//prefix matches, so go on
				int branch = (key >> prefixEnd) & 1;
				node = &n->childNodes[branch];
				prevKey = &n->keys[branch];
			} else {//insert a new node before current
				pkey = n->keys[0] & ~0xFF;
				break;
			}
		} else {//leaf
			if (*node == PTRIE_NULL_NODE) {
				*node = newNode;
				newNode->keys[0] = key;//left prefixEnd = 0, so all following insertions will be before this node
				newNode->childNodes[0] = (PTrieNode*)(value | 1);
				newNode->childNodes[1] = PTRIE_NULL_NODE;
				return;
			} else {
				pkey = *prevKey & ~0xFF;
				x = key ^ pkey;
				assert(x/*key != pkey*/ && "key already inserted");
				break;
			}
		}
	}
	BSR(index, x);
	b = (key >> index) & 1;
	newNode->keys[b] = key;
	newNode->keys[b^1] = pkey;
	newNode->keys[0] |= index;
	newNode->childNodes[b] = (PTrieNode*)(value | 1);
	newNode->childNodes[b^1] = n;
	*node = newNode;
}

static uintptr_t ptrie_remove(uintptr_t key)
{
	PTrieNode **node = &ptrieRoot;
	uintptr_t *pkey = NULL;
	assert(ptrieRoot != PTRIE_NULL_NODE && "trie is empty!");
	for (;;)
	{
		PTrieNode *n = *node;
		int branch = (key >> (n->keys[0] & 0xFF)) & 1;
		PTrieNode *cn = n->childNodes[branch];//current child node
		if ((uintptr_t)cn & 1)//leaf
		{
			PTrieNode *other = n->childNodes[branch^1];
			assert((n->keys[branch] & ~0xFF) == key);
			assert(cn != PTRIE_NULL_NODE && "node's key is probably broken");
		//	if (other == PTRIE_NULL_NODE) *node = PTRIE_NULL_NODE; else//special handling for null child nodes is not necessary
			if (((uintptr_t)other & 1) && other != PTRIE_NULL_NODE)//if other node is not a pointer
				*pkey = (n->keys[branch^1] & ~0xFF) | ((*pkey) & 0xFF);
			*node = other;
			*(PTrieNode**)n = ptrieFreeNodesList; ptrieFreeNodesList = n;//free(n);
			return (uintptr_t)cn & ~1;
		}
		pkey = &n->keys[branch];
		node = &n->childNodes[branch];
	}
}
#endif

static void *sys_aligned_alloc(size_t alignment, size_t size)
{
	void *p = VMALLOC(size);//optimistically try mapping precisely the right amount before falling back to the slow method
	assert(!(alignment & (alignment-1)) && "alignment must be a power of two");
	if ((uintptr_t)p & (alignment-1)/* && p != MAP_FAILED*/)
	{
		VMFREE(p, size);
#ifdef _WIN32
		{static DWORD allocationGranularity = 0;
		if (!allocationGranularity) {
			SYSTEM_INFO si;
			GetSystemInfo(&si);
			allocationGranularity = si.dwAllocationGranularity;
		}
		if ((uintptr_t)p < 16*1024*1024)//fill "bubbles" (reserve unaligned regions) at the beginning of virtual address space, otherwise there will be always falling back to the slow method
			VirtualAlloc(p, alignment - ((uintptr_t)p & (alignment-1)), MEM_RESERVE, PAGE_NOACCESS);
		do
		{
			p = VirtualAlloc(NULL, size + alignment - allocationGranularity, MEM_RESERVE, PAGE_NOACCESS);
			if (p == NULL) return NULL;
			VirtualFree(p, 0, MEM_RELEASE);//unfortunately, WinAPI doesn't support release a part of allocated region, so release a whole region
			p = VirtualAlloc((void*)(((uintptr_t)p + (alignment-1)) & ~(alignment-1)), size, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
		} while (p == NULL);}
#else
		p = VMALLOC(size + alignment - page_size());
		if (p/* != MAP_FAILED*/)
		{
			uintptr_t ap = ((uintptr_t)p + (alignment-1)) & ~(alignment-1);
			uintptr_t diff = ap - (uintptr_t)p;
			if (diff) VMFREE(p, diff);
			diff = alignment - page_size() - diff;
			assert((intptr_t)diff >= 0);
			if (diff) VMFREE((void*)(ap + size), diff);
			return (void*)ap;
		}
#endif
	}
	//if (p == 0) p = sys_aligned_alloc(alignment, size);//just in case (because 0 pointer is handled specially elsewhere)
	//if (p == MAP_FAILED) p = NULL;
	return p;
}

static NOINLINE void sys_free(void *p)
{
	if (p == NULL) return;
#ifdef _WIN32
	VirtualFree(p, 0, MEM_RELEASE);
#else
	SPINLOCK_ACQUIRE(&ptrieLock);
	size_t size = ptrie_remove((uintptr_t)p);
	SPINLOCK_RELEASE(&ptrieLock);
	munmap(p, size);
#endif
}

static void release_thread_cache(void*);
#ifdef __GNUC__
#include <pthread.h>
#pragma weak pthread_once
#pragma weak pthread_key_create
#pragma weak pthread_setspecific
static pthread_key_t pthread_key;
static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static void init_pthread_key() { pthread_key_create(&pthread_key, release_thread_cache); }
static thread_local int thread_initialized = 0;
static void init_pthread_destructor()//must be called only when some block placed into a thread cache's free list
{
	if (unlikely(!thread_initialized))
	{
		thread_initialized = 1;
		if (pthread_once)
		{
			pthread_once(&init_once, init_pthread_key);
			pthread_setspecific(pthread_key, (void*)1);//set nonzero value to force calling of release_thread_cache() on thread terminate
		}
	}
}
#else
static void NTAPI on_tls_callback(PVOID h, DWORD reason, PVOID pv) { h; pv; if (reason == DLL_THREAD_DETACH) release_thread_cache(0); }
#pragma comment(linker, "/INCLUDE:" CODE3264("_","") "p_thread_callback_ltalloc")
#pragma const_seg(".CRT$XLL")
extern CPPCODE("C") const PIMAGE_TLS_CALLBACK p_thread_callback_ltalloc = on_tls_callback;
#pragma const_seg()
#define init_pthread_destructor()
#endif

//End of platform-specific stuff

#define MAX_BLOCK_SIZE (MAX_BLOCK_SIZE < CHUNK_SIZE - (CHUNK_SIZE >> (1 + LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)) ? \
                        MAX_BLOCK_SIZE : CHUNK_SIZE - (CHUNK_SIZE >> (1 + LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)))
#define NUMBER_OF_SIZE_CLASSES ((sizeof(void*)*8 + 1) << LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)

typedef struct FreeBlock
{
	struct FreeBlock *next,
					 *nextBatch;//in the central cache blocks are organized into batches to allow fast moving blocks from thread cache and back
} FreeBlock;

typedef struct alignas(CACHE_LINE_SIZE) ChunkBase//force sizeof(Chunk) = cache line size to avoid false sharing
{
	unsigned int sizeClass;
} Chunk;

typedef struct alignas(CACHE_LINE_SIZE) ChunkSm//chunk of smallest blocks of size = sizeof(void*)
{
	unsigned int sizeClass;//struct ChunkBase chunk;
	struct ChunkSm *prev, *next;
	int numBatches;
#define NUM_OF_BATCHES_IN_CHUNK_SM CHUNK_SIZE/(sizeof(void*)*MAX_NUM_OF_BLOCKS_IN_BATCH)
	FreeBlock *batches[NUM_OF_BATCHES_IN_CHUNK_SM];//batches of blocks inside ChunkSm have to be stored separately (as smallest blocks of size = sizeof(void*) do not have enough space to store second pointer for the batch)
} ChunkSm;

typedef struct alignas(CACHE_LINE_SIZE)//align needed to prevent cache line sharing between adjacent classes accessed from different threads
{
	volatile int lock;
	unsigned int freeBlocksInLastChunk;
	char *lastChunk;//Chunk or ChunkSm
	union {
		FreeBlock *firstBatch;
		ChunkSm *chunkWithFreeBatches;
	};
	FreeBlock *freeList;//short list of free blocks that for some reason are not organized into batches
	unsigned int freeListSize;//should be less than batch size
	uintptr_t minChunkAddr, maxChunkAddr;
} CentralCache;
static CentralCache centralCache[NUMBER_OF_SIZE_CLASSES];// = {{0}};

typedef struct
{
	FreeBlock *freeList;
	FreeBlock *tempList;//intermediate list providing a hysteresis in order to avoid a corner case of too frequent moving free blocks to the central cache and back from
	int counter;//number of blocks in freeList (used to determine when to move free blocks list to the central cache)
} ThreadCache;
static thread_local ThreadCache threadCache[NUMBER_OF_SIZE_CLASSES];// = {{0}};

static struct
{
	volatile int lock;
	void *freeChunk;
	size_t size;
} pad = {0, NULL, 0};

static CPPCODE(inline) unsigned int get_size_class(size_t size)
{
	unsigned int index;
#if _MSC_VER && LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO == 2
	static const unsigned char small_size_classes[256] = {//have to use a const array here, because MS compiler unfortunately does not evaluate _BitScanReverse with a constant argument at compile time (as gcc does for __builtin_clz)
#if CODE3264(1, 0)
		131, 4, 15, 17, 19, 20, 21, 22, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43
#else
		131, 15, 19, 21, 23, 24, 25, 26, 27, 28, 28, 29, 29, 30, 30, 31, 31, 32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47
#endif
	};
	if (size < 256 * sizeof(void*) - (sizeof(void*)-1))
		return small_size_classes[(size + (sizeof(void*)-1)) / sizeof(void*)];
#endif

	size = (size + (sizeof(void*)-1)) & ~(sizeof(void*)-1);//minimum block size is sizeof(void*), doing this is better than just "size = max(size, sizeof(void*))"

	BSR(index, (size-1)|1);//"|1" needed because result of BSR is undefined for zero input
#if LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO == 0
	return index;
#else
	return (index<<LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO) + (unsigned int)((size-1) >> (index-LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO));
#endif
}

static unsigned int class_to_size(unsigned int c)
{
#if LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO == 0
	return 2 << c;
#else
#if LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO >= CODE3264(2, 3)
	if (unlikely(c < (LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO<<LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)))//for block sizes less than or equal to pow(2, LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)
		return 2 << (c>>LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO);
	else
#endif
	{
		c -= (1<<LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)-1;
		return ((c & ((1<<LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)-1)) | (1<<LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)) << ((c>>LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)-LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO);
	}
#endif
}

static unsigned int batch_size(unsigned int sizeClass)//calculates a number of blocks to move between a thread cache and a central cache in one shot
{
	return ((MAX_BATCH_SIZE-1) >> (sizeClass >> LTALLOC_SIZE_CLASSES_SUBPOWER_OF_TWO)) & (MAX_NUM_OF_BLOCKS_IN_BATCH-1);
}

CPPCODE(template <bool> static) void *ltmalloc(size_t size);

CPPCODE(template <bool throw_>) static void *fetch_from_central_cache(size_t size, ThreadCache *tc, unsigned int sizeClass)
{
	void *p;
	if (likely(size-1u <= MAX_BLOCK_SIZE-1u))//<=> if (size <= MAX_BLOCK_SIZE && size != 0)
	{
		FreeBlock *fb = tc->tempList;
		if (fb)
		{
			assert(tc->counter == (int)batch_size(sizeClass)+1);
			tc->counter = 1;
			tc->freeList = fb->next;
			tc->tempList = NULL;
			return fb;
		}

		assert(tc->counter == 0 || tc->counter == (int)batch_size(sizeClass)+1);
		tc->counter = 1;

		{CentralCache *cc = &centralCache[sizeClass];
		SPINLOCK_ACQUIRE(&cc->lock);
		if (unlikely(!cc->firstBatch))//no free batch
		{no_free_batch:{
			unsigned int batchSize = batch_size(sizeClass)+1;

			if (cc->freeList)
			{
				assert(cc->freeListSize);
				if (likely(cc->freeListSize <= batchSize + 1))
				{
					tc->counter = batchSize - cc->freeListSize + 1;
				//	batchSize = cc->freeListSize;
					cc->freeListSize = 0;
					fb = cc->freeList;
					cc->freeList = NULL;
				}
				else
				{
					cc->freeListSize -= batchSize;
					fb = cc->freeList;
					{FreeBlock *b = cc->freeList;
					while (--batchSize) b = b->next;
					cc->freeList = b->next;
					b->next = NULL;}
				}
				SPINLOCK_RELEASE(&cc->lock);
				tc->freeList = fb->next;
				init_pthread_destructor();//this call must be placed carefully to allow recursive memory allocation from pthread_key_create (in case when ltalloc replaces the system malloc)
				return fb;
			}

			{unsigned int blockSize = class_to_size(sizeClass);
			if (cc->freeBlocksInLastChunk)
			{
				char *firstFree = cc->lastChunk;
				assert(cc->lastChunk && cc->freeBlocksInLastChunk == (CHUNK_SIZE - ((uintptr_t)cc->lastChunk & (CHUNK_SIZE-1)))/blockSize);
				if (cc->freeBlocksInLastChunk < batchSize) {
					tc->counter = batchSize - cc->freeBlocksInLastChunk + 1;
					batchSize = cc->freeBlocksInLastChunk;
				}
				cc->freeBlocksInLastChunk -= batchSize;
				cc->lastChunk += blockSize * batchSize;
				if (cc->freeBlocksInLastChunk == 0) {
					assert(((uintptr_t)cc->lastChunk & (CHUNK_SIZE-1)) == 0);
					cc->lastChunk = ((char**)cc->lastChunk)[-1];
					if (cc->lastChunk)
						cc->freeBlocksInLastChunk = (CHUNK_SIZE - ((uintptr_t)cc->lastChunk & (CHUNK_SIZE-1)))/blockSize;
				}
				SPINLOCK_RELEASE(&cc->lock);
				fb = (FreeBlock*)firstFree;
				while (--batchSize)
					firstFree = (char*)(((FreeBlock*)firstFree)->next = (FreeBlock*)(firstFree + blockSize));
				((FreeBlock*)firstFree)->next = NULL;
				tc->freeList = fb->next;
				init_pthread_destructor();
				return fb;
			}

			//Allocate new chunk
			SPINLOCK_RELEASE(&cc->lock);//release lock for a while

			SPINLOCK_ACQUIRE(&pad.lock);
			if (pad.freeChunk)
			{
				p = pad.freeChunk;
				pad.freeChunk = *(void**)p;
				pad.size -= CHUNK_SIZE;
				SPINLOCK_RELEASE(&pad.lock);
				((char**)((char*)p + CHUNK_SIZE))[-1] = 0;
			} else {
				SPINLOCK_RELEASE(&pad.lock);
				p = sys_aligned_alloc(CHUNK_SIZE, CHUNK_SIZE);
				if (unlikely(!p)) { CPPCODE(if (throw_) throw std::bad_alloc(); else) return NULL; }
			}

#define CHUNK_IS_SMALL unlikely(sizeClass < get_size_class(2*sizeof(void*)))
			{unsigned int numBlocksInChunk = (CHUNK_SIZE - (CHUNK_IS_SMALL ? sizeof(ChunkSm) : sizeof(Chunk)))/blockSize;
#ifndef _WIN32
			//intptr_t sz = ((CHUNK_SIZE - numBlocksInChunk*blockSize) & ~(page_size()-1)) - page_size();
			//if (sz > 0) mprotect((char*)p + page_size(), sz, PROT_NONE);//munmap((char*)p + page_size(), sz);//to make possible unmapping, we need to be more careful when returning memory to the system, not simply VMFREE(firstFreeChunk, CHUNK_SIZE), so let there be just mprotect
#endif
			assert(((char**)((char*)p + CHUNK_SIZE))[-1] == 0);//assume that allocated memory is always zero filled (on first access); it is better not to zero it explicitly because it will lead to allocation of physical page which may never needed otherwise
			if (numBlocksInChunk < batchSize) {
				tc->counter = batchSize - numBlocksInChunk + 1;
				batchSize = numBlocksInChunk;
			}

			//Prepare chunk
			((Chunk*)p)->sizeClass = sizeClass;
			{char *firstFree = (char*)p + CHUNK_SIZE - numBlocksInChunk*blockSize;//blocks in chunk are located in such way to achieve a maximum possible alignment
			fb = (FreeBlock*)firstFree;
			{int n = batchSize; while (--n)
				firstFree = (char*)(((FreeBlock*)firstFree)->next = (FreeBlock*)(firstFree + blockSize));}
			((FreeBlock*)firstFree)->next = NULL;
			firstFree += blockSize;

			SPINLOCK_ACQUIRE(&cc->lock);
			if ((uintptr_t)p < cc->minChunkAddr || !cc->minChunkAddr) cc->minChunkAddr = (uintptr_t)p;
			if ((uintptr_t)p > cc->maxChunkAddr                     ) cc->maxChunkAddr = (uintptr_t)p;

			if (CHUNK_IS_SMALL)//special handling for smallest blocks of size = sizeof(void*)
			{
				ChunkSm *cs = (ChunkSm*)p;
				cs->numBatches = 0;
				//Insert new chunk right after chunkWithFreeBatches
				cs->prev = cc->chunkWithFreeBatches;
				if (cc->chunkWithFreeBatches) {
					cs->next = cc->chunkWithFreeBatches->next;
					if (cc->chunkWithFreeBatches->next) cc->chunkWithFreeBatches->next->prev = cs;
					cc->chunkWithFreeBatches->next = cs;
				} else {
					cs->next = NULL;
					cc->chunkWithFreeBatches = cs;
				}
			}

			if (unlikely(cc->freeBlocksInLastChunk))//so happened that other thread have already allocated chunk for the same size class while the lock was released
			{
				//Hook pointer to the current lastChunk at the end of new chunk (another way is just put all blocks to cc->freeList which is much less effecient)
				((char**)(((uintptr_t)firstFree & ~(CHUNK_SIZE-1)) + CHUNK_SIZE))[-1] = cc->lastChunk;
			}
			cc->freeBlocksInLastChunk = numBlocksInChunk - batchSize;
			cc->lastChunk = firstFree;
		}}}}}
		else {
			if (!CHUNK_IS_SMALL)//smallest blocks of size = sizeof(void*) are handled specially
			{
				fb = cc->firstBatch;
				cc->firstBatch = fb->nextBatch;
			}
			else//size of block = sizeof(void*)
			{
				ChunkSm *cs = cc->chunkWithFreeBatches;
				if (unlikely(cs->numBatches == 0))
				{
					if (unlikely(cs->prev == NULL)) goto no_free_batch;
					cs = cc->chunkWithFreeBatches = cs->prev;
					assert(cs->numBatches == NUM_OF_BATCHES_IN_CHUNK_SM);
				}
				fb = cs->batches[--cs->numBatches];
			}
		}
		SPINLOCK_RELEASE(&cc->lock);}
		tc->freeList = fb->next;
		init_pthread_destructor();
		return fb;
	}
	else//allocate block directly from the system
	{
		if (unlikely(size == 0)) return ltmalloc CPPCODE(<throw_>)(1);//return NULL;//doing this check here is better than on the top level

		size = (size + CHUNK_SIZE-1) & ~(CHUNK_SIZE-1);
		p = sys_aligned_alloc(CHUNK_SIZE, size);
#ifndef _WIN32
		if (p) {
			SPINLOCK_ACQUIRE(&ptrieLock);
			PTrieNode *newNode;
			if (ptrieFreeNodesList)
				ptrieFreeNodesList = *(PTrieNode**)(newNode = ptrieFreeNodesList);
			else if (ptrieNewAllocatedPage) {
				newNode = ptrieNewAllocatedPage;
				if (!((uintptr_t)++ptrieNewAllocatedPage & (page_size()-1)))
					ptrieNewAllocatedPage = ((PTrieNode**)ptrieNewAllocatedPage)[-1];
			} else {
				SPINLOCK_RELEASE(&ptrieLock);
				newNode = (PTrieNode*)VMALLOC(page_size());
				if (unlikely(!newNode)) { CPPCODE(if (throw_) throw std::bad_alloc(); else) return NULL; }
				assert(((char**)((char*)newNode + page_size()))[-1] == 0);
				SPINLOCK_ACQUIRE(&ptrieLock);
				((PTrieNode**)((char*)newNode + page_size()))[-1] = ptrieNewAllocatedPage;//in case if other thread also have just allocated a new page
				ptrieNewAllocatedPage = newNode + 1;
			}
			ptrie_insert((uintptr_t)p, size, newNode);
			SPINLOCK_RELEASE(&ptrieLock);
		}
#endif
		CPPCODE(if (throw_) if (unlikely(!p)) throw std::bad_alloc();)
		return p;
	}
}

CPPCODE(template <bool throw_> static) void *ltmalloc(size_t size)
{
	unsigned int sizeClass = get_size_class(size);
	ThreadCache *tc = &threadCache[sizeClass];
	FreeBlock *fb = tc->freeList;
	if (likely(fb))
	{
		tc->freeList = fb->next;
		tc->counter++;
		return fb;
	}
	else
		return fetch_from_central_cache CPPCODE(<throw_>)(size, tc, sizeClass);
}
CPPCODE(void *ltmalloc(size_t size) {return ltmalloc<false>(size);})//for possible external usage

static void add_batch_to_central_cache(CentralCache *cc, unsigned int sizeClass, FreeBlock *batch)
{
	if (!CHUNK_IS_SMALL)
	{
		batch->nextBatch = cc->firstBatch;
		cc->firstBatch = batch;
	}
	else
	{
		ChunkSm *cs = cc->chunkWithFreeBatches;
		if (unlikely(cs->numBatches == NUM_OF_BATCHES_IN_CHUNK_SM))
		{
			cs = cc->chunkWithFreeBatches = cc->chunkWithFreeBatches->next;
			assert(cs && cs->numBatches == 0);
		}
		cs->batches[cs->numBatches++] = batch;
	}
}

static NOINLINE void move_to_central_cache(ThreadCache *tc, unsigned int sizeClass)
{
	init_pthread_destructor();//needed for cases when freed memory was allocated in the other thread and no alloc was called in this thread till its termination

	tc->counter = batch_size(sizeClass);
	if (tc->tempList)//move temp list to the central cache
	{
		CentralCache *cc = &centralCache[sizeClass];
		SPINLOCK_ACQUIRE(&cc->lock);
		add_batch_to_central_cache(cc, sizeClass, tc->tempList);
		SPINLOCK_RELEASE(&cc->lock);
	}
// 	else if (unlikely(!tc->freeList))//this is a first call (i.e. when counter = 0) - just initialization of counter needed
// 	{
// 		tc->counter--;
// 		return;
// 	}

	tc->tempList = tc->freeList;
	tc->freeList = NULL;
}

void ltfree(void *p)
{
	if (likely((uintptr_t)p & (CHUNK_SIZE-1)))
	{
		unsigned int sizeClass = ((Chunk*)((uintptr_t)p & ~(CHUNK_SIZE-1)))->sizeClass;
		ThreadCache *tc = &threadCache[sizeClass];

		if (unlikely(--tc->counter < 0))
			move_to_central_cache(tc, sizeClass);

		((FreeBlock*)p)->next = tc->freeList;
		tc->freeList = (FreeBlock*)p;
	}
	else
		sys_free(p);
}

size_t ltmsize(void *p)
{
	if (likely((uintptr_t)p & (CHUNK_SIZE-1)))
	{
		return class_to_size(((Chunk*)((uintptr_t)p & ~(CHUNK_SIZE-1)))->sizeClass);
	}
	else
	{
		if (p == NULL) return 0;
#ifdef _WIN32
		{MEMORY_BASIC_INFORMATION mi;
		VirtualQuery(p, &mi, sizeof(mi));
		return mi.RegionSize;}
#else
		SPINLOCK_ACQUIRE(&ptrieLock);
		size_t size = ptrie_lookup((uintptr_t)p);
		SPINLOCK_RELEASE(&ptrieLock);
		return size;
#endif
	}
}

static void release_thread_cache(void *p)
{
	unsigned int sizeClass = 0; (void)p;
	for (;sizeClass < NUMBER_OF_SIZE_CLASSES; sizeClass++)
	{
		ThreadCache *tc = &threadCache[sizeClass];
		if (tc->freeList || tc->tempList)
		{
			FreeBlock *tail = tc->freeList;
			unsigned int freeListSize = 1;
			CentralCache *cc = &centralCache[sizeClass];

			if (tail)
				while (tail->next)//search for end of list
					tail = tail->next, freeListSize++;

			SPINLOCK_ACQUIRE(&cc->lock);
			if (tc->tempList)
				add_batch_to_central_cache(cc, sizeClass, tc->tempList);
			if (tc->freeList) {//append tc->freeList to cc->freeList
				tail->next = cc->freeList;
				cc->freeList = tc->freeList;
				assert(freeListSize == batch_size(sizeClass)+1 - tc->counter);
				cc->freeListSize += freeListSize;
			}
			SPINLOCK_RELEASE(&cc->lock);
		}
	}
}

void ltsqueeze(size_t padsz)
{
	unsigned int sizeClass = get_size_class(2*sizeof(void*));//skip small chunks because corresponding batches can not be efficiently detached from the central cache (if that becomes relevant, may be it worths to reimplement batches for small chunks from array to linked lists)
	for (;sizeClass < NUMBER_OF_SIZE_CLASSES; sizeClass++)
	{
		CentralCache *cc = &centralCache[sizeClass];
		if (cc->maxChunkAddr - cc->minChunkAddr <= CHUNK_SIZE)//preliminary check without lock (assume that writing to minChunkAddr/maxChunkAddr is atomic)
			continue;

		SPINLOCK_ACQUIRE(&cc->lock);
		if (cc->maxChunkAddr - cc->minChunkAddr <= CHUNK_SIZE) {//quick check for theoretical possibility that at least one chunk is totally free
			SPINLOCK_RELEASE(&cc->lock);
			continue;
		}
		{uintptr_t minChunkAddr = cc->minChunkAddr;
		size_t bufferSize = ((cc->maxChunkAddr - minChunkAddr) / CHUNK_SIZE + 1) * sizeof(short);
		//Quickly detach all batches of the current size class from the central cache
		unsigned int freeListSize = cc->freeListSize;
		FreeBlock *firstBatch = cc->firstBatch, *freeList = cc->freeList;
		cc->firstBatch = NULL;
		cc->freeList = NULL;
		cc->freeListSize = 0;
		SPINLOCK_RELEASE(&cc->lock);

		//1. Find out chunks with only free blocks via a simple counting the number of free blocks in each chunk
		{char buffer[32*1024];//enough for 1GB address space
		unsigned short *inChunkFreeBlocks = (unsigned short*)(bufferSize <= sizeof(buffer) ? memset(buffer, 0, bufferSize) : VMALLOC(bufferSize));
		unsigned int numBlocksInChunk = (CHUNK_SIZE - (/*CHUNK_IS_SMALL ? sizeof(ChunkSm) : */sizeof(Chunk)))/class_to_size(sizeClass);
		FreeBlock **pbatch, *block, **pblock;
		Chunk *firstFreeChunk = NULL;
		assert(numBlocksInChunk < (1U<<(sizeof(short)*8)));//in case if CHUNK_SIZE is too big that total count of blocks in it doesn't fit at short type (...may be use static_assert instead?)
		if (inChunkFreeBlocks)//consider VMALLOC can fail
		{
			for (pbatch = &firstBatch; *pbatch; pbatch = &(*pbatch)->nextBatch)
				for (block = *pbatch; block; block = block->next)
#define FREE_BLOCK(block) \
					if (++inChunkFreeBlocks[((uintptr_t)block - minChunkAddr) / CHUNK_SIZE] == numBlocksInChunk)/*chunk is totally free*/\
					{\
						Chunk *chunk = (Chunk*)((uintptr_t)block & ~(CHUNK_SIZE-1));\
						assert(chunk->sizeClass == sizeClass);/*just in case check before overwriting this info*/\
						*(Chunk**)chunk = firstFreeChunk;/*put nextFreeChunk pointer right at the beginning of Chunk as there are always must be a space for one pointer before first memory block*/\
						firstFreeChunk = chunk;\
					}
				FREE_BLOCK(block)
			for (pblock = &freeList; *pblock; pblock = &(*pblock)->next)
				FREE_BLOCK(*pblock)
#undef FREE_BLOCK
		}
		else {
			for (pbatch = &firstBatch; *pbatch; pbatch = &(*pbatch)->nextBatch);
			for (pblock = &freeList; *pblock; pblock = &(*pblock)->next);
		}

		if (firstFreeChunk)//is anything to release
		{
			//2. Unlink all matching blocks from the corresponding free lists
			FreeBlock *additionalBatchesList = NULL, *additionalBlocksList = NULL, **abatch = &additionalBatchesList, **ablock = &additionalBlocksList;
			unsigned int additionalBlocksListSize = 0, batchSize = batch_size(sizeClass)+1;
			for (pbatch = &firstBatch; *pbatch;)
			{
				for (block = *pbatch; block; block = block->next)
					if (inChunkFreeBlocks[((uintptr_t)block - minChunkAddr) / CHUNK_SIZE] == numBlocksInChunk)//if at least one block belongs to a releasable chunk, then this batch should be handled specially
					{
						FreeBlock *nextBatch = (*pbatch)->nextBatch;
						for (block = *pbatch; block;)//re-add blocks of not-for-release chunks and organize them into another batches' list (to join it with the main later)
							if (inChunkFreeBlocks[((uintptr_t)block - minChunkAddr) / CHUNK_SIZE] != numBlocksInChunk)//skip matching-for-release blocks
							{
								*ablock = block;
								do//this loop needed only to minimize memory write operations, otherwise a simpler approach could be used (like in the next loop below)
								{
									ablock = &block->next;
									block = block->next;
									if (++additionalBlocksListSize == batchSize)
									{
										abatch = &(*abatch = additionalBlocksList)->nextBatch;
										*abatch = NULL;
										*ablock = NULL;
										ablock = &additionalBlocksList;
										additionalBlocksList = NULL;
										additionalBlocksListSize = 0;
										break;//to force *ablock = block; for starting a new batch
									}
								} while (block && inChunkFreeBlocks[((uintptr_t)block - minChunkAddr) / CHUNK_SIZE] != numBlocksInChunk);
							}
							else
								block = block->next;
						*ablock = NULL;
						*pbatch = nextBatch;//unlink batch
						goto continue_;
					}
				pbatch = &(*pbatch)->nextBatch;
continue_:;
			}
			for (block = freeList; block;)
				if (inChunkFreeBlocks[((uintptr_t)block - minChunkAddr) / CHUNK_SIZE] != numBlocksInChunk)
				{
					//*pblock = (*pblock)->next, freeListSize--;//unlink block
					ablock = &(*ablock = block)->next;
					block = block->next;
					*ablock = NULL;
					if (++additionalBlocksListSize == batchSize)
					{
						abatch = &(*abatch = additionalBlocksList)->nextBatch;
						*abatch = NULL;
						ablock = &additionalBlocksList;
						additionalBlocksList = NULL;
						additionalBlocksListSize = 0;
					}
				}
				else
					block = block->next;
			//Add additional lists
			*abatch = *pbatch;
			*pbatch = additionalBatchesList;
			pblock = ablock;
			freeList = additionalBlocksList;
			freeListSize = additionalBlocksListSize;

			//Return back all left not-for-release blocks to the central cache as quickly as possible (as other threads may want to allocate a new memory)
#define GIVE_LISTS_BACK_TO_CC \
			SPINLOCK_ACQUIRE(&cc->lock);\
			*pbatch = cc->firstBatch;\
			cc->firstBatch = firstBatch;\
			*pblock = cc->freeList;\
			cc->freeList = freeList;\
			cc->freeListSize += freeListSize;\
			SPINLOCK_RELEASE(&cc->lock);\
			if (bufferSize > sizeof(buffer)) VMFREE(inChunkFreeBlocks, bufferSize);//this better to do before 3. as kernel is likely optimized for release of just allocated range
			GIVE_LISTS_BACK_TO_CC

			if (padsz)
			{
				SPINLOCK_ACQUIRE(&pad.lock);
				if (pad.size < padsz)
				{
					Chunk *first = firstFreeChunk, **c;
					do//put off free chunks up to a specified pad size
					{
						c = (Chunk**)firstFreeChunk;
						firstFreeChunk = *c;
						pad.size += CHUNK_SIZE;
					} while (pad.size < padsz && firstFreeChunk);
					*c = (Chunk*)pad.freeChunk;
					pad.freeChunk = first;
				}
				SPINLOCK_RELEASE(&pad.lock);
			}

			//3. Return memory to the system
			while (firstFreeChunk)
			{
				Chunk *nextFreeChunk = *(Chunk**)firstFreeChunk;
				VMFREE(firstFreeChunk, CHUNK_SIZE);
				firstFreeChunk = nextFreeChunk;
			}
		}
		else//nothing to release - just return batches back to the central cache
		{
			GIVE_LISTS_BACK_TO_CC
#undef GIVE_LISTS_BACK_TO_CC
		}}}
	}
}

#if defined(__cplusplus) && !defined(LTALLOC_DISABLE_OPERATOR_NEW_OVERRIDE)
void *operator new  (size_t size) throw(std::bad_alloc)          {return ltmalloc<true> (size);}
void *operator new  (size_t size, const std::nothrow_t&) throw() {return ltmalloc<false>(size);}
void *operator new[](size_t size) throw(std::bad_alloc)          {return ltmalloc<true> (size);}
void *operator new[](size_t size, const std::nothrow_t&) throw() {return ltmalloc<false>(size);}

void operator delete  (void* p)                        throw() {ltfree(p);}
void operator delete  (void* p, const std::nothrow_t&) throw() {ltfree(p);}
void operator delete[](void* p)                        throw() {ltfree(p);}
void operator delete[](void* p, const std::nothrow_t&) throw() {ltfree(p);}
#endif

/* @r-lyeh's { */
#include <string.h>
void *ltcalloc(size_t elems, size_t size) {
	size *= elems;
	return memset( ltmalloc( size ), 0, size );
}
void *ltmemalign( size_t align, size_t size ) {
	return --align, ltmalloc( (size+align)&~align );
}
void *ltrealloc( void *ptr, size_t sz ) {
	if( !ptr ) return ltmalloc( sz );
	if( !sz  ) return ltfree( ptr ), (void *)0;
	size_t osz = ltmsize( ptr );
	if( sz <= osz ) {
		return ptr;
	}
	void *nptr = memcpy( ltmalloc(sz), ptr, osz );
	ltfree( ptr );

#ifdef LTALLOC_AUTO_GC_INTERVAL
	/* this is kind of compromise; the following timer is to guarantee
	that memory gets wiped out at least every given seconds between consecutive 
	ltrealloc() calls (I am assuming frequency usage for ltrealloc() is smaller
	than ltmalloc() or ltfree() too) - @r-lyeh */
			clock_t now = clock();
	static	clock_t then = now;
	if( ( double(now - then) / CLOCKS_PER_SEC ) > LTALLOC_AUTO_GC_INTERVAL ) {
		ltsqueeze(0);
	}
	then = now;
#endif

	return nptr;
}
/* } */
