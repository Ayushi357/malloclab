/*
 * mm.c
 *
 * Name: Ayushi Agrawal [aja6540], Adithya Krishnan Kannan [apk5863]
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * Also, read malloclab.pdf carefully and in its entirety before beginning.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* Basic constants and macros to manipulate the free list*/
// Taken from the book CSAPP with some minor changes, but the functionalities are the same
#define WSIZE 8 /* Word and header/footer size (bytes) */
#define DSIZE 16 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

static void* heap_listp;

typedef struct LinkedList {
    struct LinkedList* prev;
    struct LinkedList* next;
} LinkedList;

static LinkedList* head;
static LinkedList* tail;


static inline unsigned long MAX(size_t x, size_t y) {
    return ((x) > (y)? (x) : (y));
}

/* Pack a size and allocated bit into a word */
static inline unsigned long PACK(size_t size, int alloc) {
    return ((size) | (alloc));
}

/* Read and write a word at address p */
static inline unsigned long GET(void *p) {
    return (*(unsigned int *)(p));
}

static inline void PUT(void* p, unsigned long val) {
    (*(unsigned int *)(p) = (val));
}

/* Read the size and allocated fields from address p */
static inline unsigned long GET_SIZE(void* p) {
    return (GET(p) & ~0x7);
}

static inline unsigned long GET_ALLOC(void* p) {
    return (GET(p) & 0x1);
}

/* Given block ptr bp, compute address of its header and footer */
static inline void* HDRP(void* bp) {
    return ((void *)(bp) - WSIZE);
}

static inline void* FTRP(void* bp) {
    return ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

/* Given block ptr bp, compute address of next and previous blocks */
static inline void* NEXT_BLKP(void* bp) {
    return ((void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void* bp) {
    return ((void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)));
}

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Initialize: returns false on error, true on success.
 */

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { /* Case 1: Both the block are allocated */
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2: Prev is allocated, but next is not, so remove the next & current block */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3: next is allocated but previous is not, so remove current and prev block */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else { /* Case 4: all free */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}


/*2. Extend Heap Function (Taken from book as well): this extends the heap with a new free block
It utilizes the PUT function to initialize the header, footer to extend the heap in malloc*/

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*3. Find Fit Function (similar to book): this function find the available space in the heap and return*/

static void *find_fit(size_t asize)
{
    /* First-fit search */
    //void *bp;
    LinkedList *ptr = head;

    while(ptr != NULL) {
        if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            return ptr;
        }
    }
    ptr = ptr->next;

return NULL; /* No fit */
}

/*4. Place Function (similar to book): It uses the ptr to the requested block, and split the blocks if$
to the minimum block size*/

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }

    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * Initialize: returns false on error, true on success.
 */

// From book as well, just made some minor changes: creates a heap with initial free block
// The function gets four words from the memory system and initializes them to create the empty free l$


bool mm_init(void)
{
    /* IMPLEMENT THIS */
    head = NULL;
    tail = NULL;
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1) {
        return false;
    }

    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */

    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return false;
    }
    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    /* IMPLEMENT THIS */
    size_t asize; /* Adjusted block size */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    if ((bp = extend_heap(asize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(void* ptr)
{
    /* IMPLEMENT THIS */
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    size_t oldsize = GET_SIZE(oldptr);

    if(oldptr == NULL) {
        oldptr = malloc(size);
    }

    else if (size == 0) {
        free(oldptr);
    }

    else if(oldsize < size) {
        void* p = malloc(size);
        mem_memcpy(p, oldptr, oldsize);
        free(oldptr);
        return p;
    }

    else {
        oldsize = size;
        void* p = malloc(oldsize);
        mem_memcpy(p, oldptr, oldsize);
        free(oldptr);
        return p;
    }
    return NULL;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
#endif /* DEBUG */
    return true;
}






