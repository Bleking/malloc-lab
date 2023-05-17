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

// mdriver 구동을 위한 team정보 struct 설정
team_t team = {
    /* Team name */
    "week06_team2",
    
    /* First member's full name */
    "Young woo Kim",
    /* First member's email address */
    "uddn@naver.com",
    
    /* Third member's full name (leave blank if none) */
    "Jun ho Shin",
    /* Third member's email address (leave blank if none) */
    "sjunho98@gmail.com"
};

// 각종 변수, 함수 설정
#define WSIZE 4 // word and header footer 사이즈를 byte로.
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산)
#define PACK(size, alloc) ((size) | (alloc))

/* address p위치에 words를 read와 write를 한다. */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* given block ptr bp, 그것의 header와 footer의 주소를 계산*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp = 0;
static char *start_nextfit = 0;  // next-fit 사용

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)  // heap_listp의 시작 주소 변경
        return -1;
    
    PUT(heap_listp, 0);  // Alignment padding; 더블 워드 경계로 정렬된 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  // Prologue header; 8바이트 할당 블록
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // Prologue footer; 8바이트 할당 블록
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));  // Epilogue header
    heap_listp += (2*WSIZE);
    start_nextfit = heap_listp;
    
    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;  // 실패하면
    return 0;  // 성공하면
}


static void *coalesce(void *bp) {  // 가용 블록 합치기
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));
    
    // case 1 - 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
    if (prev_alloc && next_alloc) {
        start_nextfit = bp;
        return bp;  // size 값은 현재 bp의 크기
    }
    // case2 - 이전 블록은 할당 상태, 다음 블록은 가용상태. 현재 블록은 다음 블록과 통합
    else if (prev_alloc && !next_alloc) {                                        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 크기: 현재 블록 크기 + 다음 블록의 크기
        PUT(HDRP(bp), PACK(size, 0));  // 현재 블록 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0));  // 다음 불록 푸터 갱신
    }
    // case 3 - 이전 블록은 가용상태, 다음 블록은 할당 상태. 이전 블록을 현재 블록과 통합
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 크기: 이전 블록의 크기 + 현재 블록의 크기
        PUT(FTRP(bp), PACK(size, 0));  // 현재 블록의 푸터
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더
        bp = PREV_BLKP(bp);  // 이전 (가용) 블록으로 이동
    }
    // case 4 - 이전 블록과 다음 블록 모두 가용상태. 이전, 현재, 다음 3개의 블록 모두 하나의 가용 블록으로 통합
    else {                                                                        
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));  // 크기: 이전 블록 헤더, 다음 블록 푸터 까지 합치기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  // 다음 블록의 푸터
        bp = PREV_BLKP(bp);  // 이전 (가용) 블록으로 이동
    }
    start_nextfit = bp;
    return bp;
}
static void *extend_heap(size_t words) {  // 새 가용 블록으로 힙 확장
    char *bp;
    size_t size;
    
    // alignment 유지를 위해 짝수 개수의 words를 Allocate
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;  // (words + 1) * WSIZE: words 값이 홀수일 경우 double word 단위로 정렬
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
  
    // free block 헤더와 푸터를 init하고 epilogue 헤더를 init
    PUT(HDRP(bp), PACK(size, 0));  // free block header
    PUT(FTRP(bp), PACK(size, 0));  // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // new epilogue header 추가
  
    // prev block이 free면 coalesce
    return coalesce(bp);
}
static void *find_fit(size_t asize) {  // next fit
    void *bp;
    
    for (bp = start_nextfit; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {  // 검색이 끝났던 블록에서부터 시작
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    for (bp = heap_listp; bp != start_nextfit; bp = NEXT_BLKP(bp)) {  // 찾지 못했으면 처음부터 다시 탐색
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    
    return NULL;
}
static void place(void *bp, size_t asize) {  // 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
    // 맞는 블록을 찾으면 요청한 블록을 배치하고 초과부분을 분할한다.
    size_t csize = GET_SIZE(HDRP(bp));  // 현재 가용 블록의 크기
    // asize: malloc으로 할당한 사이즈
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));  // bp 헤더에 asize 할당
        PUT(FTRP(bp), PACK(asize, 1));  // bp 푸터에 asize 할당
        bp = NEXT_BLKP(bp);  // 다음 블록
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {  // (csize - asize) < (2 * DSIZE)
        // 할당하고 남은 블록이 더블워드*2 보다 작다며 나누지 않고 할당
        // 남은 블록이 더블워드*2 보다 작은 경우는 데이터를 담을 수 없음
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;  // 블록 사이즈 조정
    size_t extendsize;  // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;
    
    // 거짓된 요청 무시
    if (size == 0)
        return NULL;  // 할당할 블록이 없기 때문에
    // overhead, alignment 요청 포함해서 블록 사이즈 조정
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else  // size > DSIZE
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);  // 16, 24, 32, ... double word 단위로 정렬
    
    // fit에 맞는 free 리스트를 찾는다
    if ((bp = find_fit(asize)) != NULL) {  // 할당 공간을 찾고 그 주소를 bp에 입력
        place(bp, asize);
        return bp;
    }
    
    // fit 맞는게 없으면 메모리를 더 가져와 block을 위치
    extendsize = MAX(asize, CHUNKSIZE);  // find_fit 함수로 적합한 곳을 찾지 못하면 brk pointer를 증가시켜야 함
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  // brk pointer를 키우지 못하면
        return NULL;
    place(bp, asize);  // brk pointer를 높이는데 성공하면 실행
    
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;  // 기존 포인터
    void *newptr;  // 새로운 포인터
    size_t copySize;  // 기존 포인터의 크기
  
    newptr = mm_malloc(size);  // 기존의 ptr의 블록 크기를 mm_malloc으로 받아온 size 로 바꿔줌
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)  // ptr의 블록 크기가(copySize) 받아온 size보다 크면
        copySize = size;  // 받아온 size를 기존의 크기에 할당: 불필요한 메모리 공간을 침범하는 경우 방지 목적
    memcpy(newptr, oldptr, copySize);  // 기존의 ptr 데이터릏  newptr에 저장함
    mm_free(oldptr);  // 기존 데이터는 새 블록에 저장해놓고 나서 반환
    
    return newptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {  // 블록을 반환하고 경계 태그 연결 사용 -> 상수 시간 안에 인접한 가용 블록들과 통합하는 함수들
    size_t size = GET_SIZE(HDRP(bp));  // 현재 bp의 블록의 크기
    
    PUT(HDRP(bp), PACK(size, 0));  // 현재 블록의 header 반환
    PUT(FTRP(bp), PACK(size, 0));  // 현재 블록의 footer 반환
    coalesce(bp);
}
