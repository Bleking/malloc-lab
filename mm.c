/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "week06_team2",
    
    /* First member's full name */
    "YW",
    /* First member's email address */
    "yh@email.com",
    
    /* Third member's full name (leave blank if none) */
    "JH",
    /* Third member's email address (leave blank if none) */
    "jh@email.com"
};

// Basic constants and macros
#define WSIZE 8  // word and header/footer size (bytes)
#define DSIZE 16  // Double word size (bytes)
#define CHUNKSIZE (1<<12)  // Extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y)? (x):(y))

//Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))  // OR operation; 크기와 할당 비트 통합 -> 헤더와 풋터에 저장할 수 있는 값 리턴

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))  // p가 가리키는 것의 값
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p가 참조하는 워드 리턴; 포인터 p가 가리키는 포인터에 val 입력; pointer=(unsigned int *)(p) -> *pointer = val

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)  //  ~0x00000111 -> 0x11111000와 and연산하면 size나옴
#define GET_ALLOC(p) (GET(p) & 0x1)  // 할당 비트

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)  // 블록 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 블록 풋터를 가리키는 포인터 리턴; 헤더+데이터+풋터 -(헤더+풋터);

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ( (char *)(bp) + GET_SIZE(( (char *)(bp) - WSIZE )) )  // 다음 블록 포인터
#define PREV_BLKP(bp) ( (char *)(bp) - GET_SIZE(( (char *)(bp) - DSIZE )) )  // 이전 블록 포인터

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/* 
 * mm_init - initialize the malloc package.
 */
static void *heap_listp;
static char *next_heap_listp;
 
int mm_init(void) {  // 최초 가용 블록으로 힙 생성하기; 할당기 초기화
    // Create the initlal empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)
       return -1;
    
    PUT(heap_listp, 0);  // Alignment padding; 더블 워드 경계로 정렬된 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  // Prologue header; 8바이트 할당 블록
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // Prologue footer; 8바이트 할당 블록
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));  // Epilogue header
    heap_listp += (2*WSIZE);  // prologue header 뒤로
    // next_heap_listp = heap_listp;  // next_fit용으로 초기 포인터 위치 입력
    
    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
       return -1;  // 실패하면
    
    return 0;  // 성공하면
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // case 1 : 현재만 반환할 때
    if (prev_alloc && next_alloc)
        return bp;
    
    // case 2 : 다음 블록과 병합
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0)); 
        bp = PREV_BLKP(bp);  // bp를 prev로 옮김
    }
    
    // case 3 : 이전 블록과 병합
    else if(!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    // case 4 : 이전 블록과 다음 블록 병합
    else {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    return bp;
}
static void *extend_heap(size_t words) {  // 새 가용 블록으로 힙 확장하기
    char *bp;
    size_t size;
    
    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    
    // Coalesce if the previous block was free
    return coalesce(bp);
}
static void *find_fit(size_t asize) {  // first-fit, next-fit, best-fit
    // 적절한 가용 블록을 검색하고 가용블록의 주소를 반환한다
    
    /**/
    // 1. first-fit: 리스트 처음부터 탐색하여 가용블록 찾기
    void *bp;
    
    //헤더의 사이즈가 0보다 크다. -> 에필로그까지 탐색한다.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
    
    /*
    // 2. next_fit
    char *bp;
    
    for (bp = NEXT_BLKP(next_heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
    */
    /*
    // 3. best_fit
    void *bp;
    void *best_fit = NULL;
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit)))
                best_fit = bp;
        }
    }
    return best_fit;
    */
}
static void place(void *bp, size_t asize) {
    // 맞는 블록을 찾으면 요청한 블록을 배치하고 초과부분을 분할한다.
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2*DSIZE)) {
        //가용 블록에 사이즈 - 요청한 블록의 사이즈 각 더블워드*2 크거나 같을때
        //요청 블록을 넣고 남은 사이즈는 가용 블록으로 분할
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        // next-fit
        // next_heap_listp = bp;
        PUT(HDRP(bp), PACK(csize- asize, 0));
        PUT(FTRP(bp), PACK(csize- asize, 0));
    }
    else {
        //할당하고 남은 블록이 더블워드*2보다 작다며 나누지 않고 할당
        // 남은 블록이 더블워드*2보다 작은 경우는 데이터를 담을 수 없음
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp),PACK(csize, 1));
        // next-fit
        // next_heap_listp = NEXT_BLKP(bp);  //분할 이후 그 다음 블록
    }
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {  // 가용 리슽에서 블록 할당하기
    size_t asize;
    size_t extendsize;
    char *bp;
    
    if (size == 0)
        return NULL;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    
    return bp;
    /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {  // 블록을 반환하고 경계 태그 연결을 사용해서 상수 시간에 인접 가용 블록들과 통합
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr; // void *old_bp = bp;
    void *newptr;  // void *new_bp;
    size_t copySize;
    
    newptr = mm_malloc(size);  // new_bp = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);  // copySize = GET_SIZE(HDRP(old_bp));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);  // memcpy(new_bp, old_bp, copySize);
    mm_free(oldptr);  // mm_free(old_bp);
    return newptr;  // return new_bp;
}
