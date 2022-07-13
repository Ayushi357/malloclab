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

/* Basic Constants */
#define WSIZE 8 /* Word and header/footer size (bytes) */
#define DSIZE 16 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (byte) */

static void* heap_listp;

typedef struct LinkedList_s {
    struct LinkedList_s* prev;
    struct LinkedList_s* next;
	struct LinkedList_s* curr;
	struct LinkedList_s* node;
} LinkedList;

static LinkedList* head;
static LinkedList* tail;

/*To implement Explicit Free List */

/* Append a Block*/
// In this function we are adding a block of to the explicit free list.
// This function checks whether the list is empty and then the tail and head points to the newly added block
// List should be stored within the free payload, so that it doesn't utilize more space
// And if the list is not empty, use LIFO to add all free blocks to tail. 

void append_block(LinkedList *bp) {
	bp->next = NULL;
	bp->prev = NULL;
	bp->curr = head;
	bp->node = bp->curr;
	if (head == NULL && bp->curr == head) {
		head = bp;
		tail = bp;
		bp->curr = NULL;
		bp->next = NULL;
		bp->prev = NULL;
		bp->node = NULL;
	}

	else {
		tail->next = bp;
		bp->prev = tail;
		tail = bp;
		bp->next = NULL;
		bp->curr = NULL;
	}
}

/* Delete a block */
// Removes a block from the explicit free list.
// Removal of a block can have different possible cases like: remove from head, set head and tail == NULL
// Remove from head with more nodes, update the head to the next node
// Remove from tail, update the tail
// Remove from the middle of the linked list: set prev and next accordingly using pointer arithmetic

void delete_block(LinkedList *bp) {
	// Case 1: only one head node present
	bp->curr = head;
	bp->node = bp->curr;

	if (bp == head && bp == tail && bp->curr == head) {
		tail = NULL;
		head = NULL;
		bp->curr = NULL;
		bp->node = NULL;
	}

	// Case 2: at the end of the list
	else if (bp == tail && bp->curr == head) {
		bp->curr = NULL;
		bp->node = NULL;
		bp->prev->next = NULL;
		tail = tail->prev;
	}

	// Case 3: other nodes than head also present, therefore set both to NULL
	else if (bp == head && bp != tail && bp->curr == head) {
		bp->curr = NULL;
		bp->node = NULL;
		bp->next->prev = NULL;
		head = head->next;
	}
	
	else {
		// Case 4: node in the middle of the list
		bp->curr = NULL;
		bp->node = NULL;
		bp->next->prev = bp->prev;
		bp->prev->next = bp->next;
	}
}

/* Macro Functions: defined in book with some changes */

static inline unsigned long MAX(size_t x, size_t y)
{
	return ((x) > (y) ? (x) : (y));
}

/* PACK a size and allocated bit into a word */
static inline unsigned long PACK(size_t size, int alloc)
{
	return ((size) | (alloc));
}

/* Read and write a word at an address p */

static inline unsigned long GET(void* p)
{
	return (*(unsigned long *)(p));
}


static inline void PUT(void* p, unsigned long val)
{
	(*(unsigned long *)(p) = (val));
}

/* Read the size and allocated fields from address p */

static inline unsigned long GET_SIZE(void* p)
{
	return (GET(p) & ~0x7);
}

static inline unsigned long GET_ALLOC(void* p)
{
	return (GET(p) & 0x1);
}

/* Given block ptr bp, compute address of its header and footer */
static inline void* HDRP(void* bp)
{
	return ((void *)(bp) - WSIZE);
}

static inline void* FTRP(void* bp)
{
	return ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

/* Given block ptr bp, compute address of next and previous blocks */
static inline void* NEXT_BLKP(void* bp)
{
	return ((void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)));

}

static inline void* PREV_BLKP(void* bp)
{
	return ((void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)));
}

/*
 * Implementing some Helper functions
 */

/*1. Coalesce Function */
// Considering the explicit free list, we have to correctly add and remove the blocks and update the list
// Coalesce the free bloacks based on their start and end address

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	if (prev_alloc && next_alloc) {
		/* Case 1: Both the block are allocated */
		return bp;
	}
	
	else if (prev_alloc && !next_alloc) {
		/* Case 2: Prev is allocated, but next is not, so remove the next & current block */
		delete_block((LinkedList *)(bp));
		delete_block((LinkedList *)NEXT_BLKP((bp)));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
		}
	
	else if (!prev_alloc && next_alloc) {
		/* Case 3: next is allocated but previous is not, so remove current and prev block */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		delete_block((LinkedList *)(bp));
		delete_block((LinkedList *)(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp); /* Update bp */
	}
	
	else {
		/* Case 4: all free */
		delete_block((LinkedList *)PREV_BLKP((bp)));
		delete_block((LinkedList *)(bp));
		delete_block((LinkedList *)NEXT_BLKP((bp)));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp); /* Update bp */
	}

	append_block((LinkedList *)(bp)); 
	return bp;
}


/*2. Extend Heap Function (Taken from book as well): this extends the heap with a new free block
It utilizes the PUT function to initialize the header, footer to extend the heap in malloc*/

static void *extend_heap(size_t words)
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	append_block((LinkedList *)(bp)); /* Add to explicit free list */
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*3. Find Fit Function (similar to book): this function find the available space in the heap and return*/

static void *find_fit(size_t asize)
{
	/* First-fit search */
    //void *bp;
	LinkedList *ptr = head; /* Start of the list */

	while (ptr != NULL) {
		if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) { 
			return ptr;
		}
		ptr = ptr->next; // In order to iterate the while loop
	}
	return NULL; /* No fit */
}

/*4. Place Function (similar to book): It uses the ptr to the requested block, and split the blocks if$
to the minimum block size*/

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	if ((csize - asize) >= (2*DSIZE)) {
		// Case when requested size is unable to fit in current block
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		// Remove the block
		delete_block((LinkedList *)(bp));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		append_block((LinkedList *)(bp));

	}
	else {
		// fit it in the current block
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		delete_block((LinkedList *)(bp)); /* Delete the block when allocation is done */
	}
}

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Initialize: returns false on error, true on nextess.
 */
// From book as well, just made some minor changes: creates a heap with initial free block
// The function gets four words from the memory system and initializes them to create the empty free l$

bool mm_init(void)
{
	/* IMPLEMENT THIS */
	head = NULL;
	tail = NULL;
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
		return false;
	}
	
	PUT(heap_listp, 0);	/* Alignment padding */ 
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
//	size_t extendsize;
	void *bp;

	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
        asize = 2*DSIZE;
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
// This function is also taken from the book. Just added the append_block function to update the explicit free list
void free(void* ptr)
{
	size_t size = GET_SIZE(HDRP(ptr));
	
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));

	// Add the block to the explicit free list
	append_block((LinkedList *)(ptr));
	// Coalesce the blocks afterwards
	coalesce(ptr);
}

/*
 * realloc
 */
// This function will check the given cases in the handout
// If the ptr == NULL, then malloc the size and when size is 0, free the ptr
// next case is to check if the size that is requested is greater than or less than the curr_size
// set a ptr to malloc the size using mem_memcpy in order to copy the info and free the ptr

void* realloc(void* oldptr, size_t size)
{
	/* IMPLEMENT THIS */
	size_t oldsize = GET_SIZE(oldptr);
	size_t asize = size;

	if (oldptr == NULL && asize == size){
		oldptr = malloc(size);
	}

	else if (asize == size && size == 0) {
		// Just free the oldptr
		free(oldptr);
	}
	else if (oldsize < size && oldsize < size) {
		// We have malloc the given size and the pointer will point to it
		void* ptr = malloc(size);
		//  mem_memcpy in order to copy the info and free the ptr
		mem_memcpy(ptr, oldptr, oldsize);
		free(oldptr);
		return ptr;
	}
	else {
		oldsize = size;
		asize = size;
		void* ptr = malloc(oldsize);
		mem_memcpy(ptr, oldptr, oldsize);
		free(oldptr);
		return ptr; 
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
