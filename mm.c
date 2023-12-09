/*

  BLOK WOLNY:
  |HEADER(word_t) NEXT_FREE(word_t) PREV_FREE(word_t) ..... FOOTER(word_t)|
  BLOK ZAJĘTY:
  |HEADER(word_t) PAYLOAD...|

  NEXT_FREE i PREV_FREE to zrzutowanie pointery (bo wiemy ze heap < 4GiB zatem
  miesci sie w 32b jak odejmiemy 2^32) HEADER i FOOTER zawierają size i flagi
  opisane w strukturze bt_flags


  Zwalnianie bloku polega na złączenia go z poprzednim(jeżeli jest wolny) i z
  następnym(jeżeli jest wolny) i dodaniu danego bloku do odpowiedniego kubełka


  Mam następujące kubełki:
  0-64 -> pierwszy
  65-128 -> drugi
  ...
  ...
  ...

  Wyszukiwanie to prosty for po potęgach dwójki

  Dodawanie do kubełka tak samo -> zwykła lista 2 kierunkowa
  Usuwanie to samo


  Trzymam kubełki na początku heapa przed dostępnym do użytkownika miejscem
*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include <math.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *last; /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

// size bloku
static inline size_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

// wolny blok
static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

// kasowanie flagi prev_free
static inline void bt_clr_prevfree(word_t *bt) {
  *bt &= ~PREVFREE;
}

// ustawianie flagi prev_free
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  // boundary tag header
  *bt = size | flags;
  // boundary tag footer + jeżeli blok jest zajęty to nie ustawiawmy footera
  *(word_t *)((void *)bt + (bt_size(bt) - sizeof(word_t)) * bt_free(bt)) =
    size | flags;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  return (void *)bt +
         bt_size(bt); // jezeli nastepny blok wychodzi za heap_end to lipa fest
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  return (void *)bt -
         bt_size(bt -
                 1); // jezeli nastepny blok wychodzi za heap_end to lipa fest
}

/* --=[ miscellanous procedures ]=------------------------------------------ */
/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (size + sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  // mały blok pamięci żeby nie bawić się nullami dla bt_next
  bt_make(ptr + size - ALIGNMENT, ALIGNMENT, USED);
  return ptr - ALIGNMENT;
}

/* --=[ segregated fits ]=-------------------------------------------- */
// 12 kubełków
#define CLASSES 12

static word_t **class_table;

// wyszukiwanie odpowiedniego kubełka zwykły for
static inline int get_class(size_t size) {
  int class_index = 0;
  for (size_t class_size = 64; class_index < CLASSES - 1;
       class_index++, class_size <<= 1)
    if (class_size >= size)
      break;
  return class_index;
}

// rzutowanie pointera np z 0x800000abc na 0x000000abc
static inline word_t get_pointer(word_t *block) {
  return (long)block;
}

// kolejny blok w danym kubełku
// jeżeli nie ma to jest wpisane 0 -> zwracamy nulla
static inline word_t *get_next_free_ptr(word_t *bt) {
  word_t ptr = *(bt + 1);
  return ptr ? (word_t *)(0x800000000 | ptr) : NULL;
}

// ustawiamy pointer skrocony na kolejny blok
static inline void set_next_free_ptr(word_t *bt, word_t ptr) {
  *(bt + 1) = ptr;
}

// to samo co na nastepny
static inline word_t *get_prev_free_ptr(word_t *bt) {
  word_t ptr = *(bt + 2);
  return ptr ? (word_t *)(0x800000000 | ptr) : NULL;
}

// to samo co na nastepny
static inline void set_prev_free_ptr(word_t *bt, word_t ptr) {
  *(bt + 2) = ptr;
}

// dodawanie do kubełka
static inline void add_on_class_list(word_t *block) {
  // pobieramy index odpowiedniego kubełka
  int class_index = get_class(bt_size(block));
  // jeżeli jest juz jakis element to po prostu dodajemy
  if (class_table[class_index]) {
    set_prev_free_ptr(class_table[class_index], get_pointer(block));
    set_next_free_ptr(block, get_pointer(class_table[class_index]));
    set_prev_free_ptr(block, 0);
  } else { // w przeciwnym razie wrzucamy jako pierwszy element w kuble
    set_next_free_ptr(block, 0);
    set_prev_free_ptr(block, 0);
  }
  // ustawiamy na poczatek kubla ostatnio dodany blok
  class_table[class_index] = block;
  // ustawiamy flage prev_free
  word_t *next = bt_next(block);
  bt_set_prevfree(next);
}

// usuwanie z kubła
static inline void del_from_class_list(word_t *block) {
  // tak samo pobieramy index odpwoiedniego kubła
  int class_index = get_class(bt_size(block));
  // pobieramy kolejny i poprzedni wolny blok
  word_t *prev = get_prev_free_ptr(block);
  word_t *next = get_next_free_ptr(block);

  // i odpowiednio przepinamy
  if (!prev && !next) {
    class_table[class_index] = NULL;
  } else if (!prev && next) {
    class_table[class_index] = next;
    set_prev_free_ptr(next, 0);
  } else if (prev && !next) {
    set_next_free_ptr(prev, 0);
  } else {
    set_next_free_ptr(prev, get_pointer(next));
    set_prev_free_ptr(next, get_pointer(prev));
  }
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  // allocowanie miejsca na kubełki
  if ((class_table = mem_sbrk(CLASSES * sizeof(word_t *))) == NULL)
    return -1;
  // wszystkie ustawiamy na puste
  for (int i = 0; i < CLASSES; i++)
    class_table[i] = NULL;

  // padding zeby payloady dobrze sie zaczynaly
  word_t *ptr = mem_sbrk(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;
  // ustawiamy padding na USED wtedy przy bt_prev nie musimy bawic sie z nullami
  bt_make(ptr, ALIGNMENT - sizeof(word_t), USED);

  // epilog
  ptr = mem_sbrk(ALIGNMENT);
  if (!ptr)
    return -1;
  *ptr = ALIGNMENT;
  // ustawiamy last'a na nulla
  last = NULL;

  // optymalizacja pod ślady żeby lepiej się układały bloki
  // mozna tez free(malloc(64));
  word_t *tmp = morecore(64);
  bt_make(tmp, 64, FREE);
  add_on_class_list(tmp);

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
// prosty find fit przechodzimy przez wszystkie kubełki od pierwszego pasującego
static word_t *find_fit(size_t reqsz) {
  word_t *block;
  for (int class_index = get_class(reqsz); class_index < CLASSES;
       class_index++) {
    block = class_table[class_index];
    while (block) {
      if (bt_size(block) >= reqsz)
        return block;
      block = get_next_free_ptr(block);
    }
  }
  return block;
}
#else
/* Best fit startegy. */
// to samo co find-fit tylko w tym przypadku jezeli znajdziemy blok to
// przechodzimy do konca kubelka zeby przeszukac jeszcze inne bloki i zwracamy
// po przejsciu calego kubla
static word_t *find_fit(size_t reqsz) {
  word_t *block;
  word_t *min_block = NULL;
  size_t min_block_size = INT64_MAX;
  for (int class_index = get_class(reqsz); class_index < CLASSES;
       class_index++) {
    block = class_table[class_index];
    while (block) {
      if (bt_size(block) >= reqsz && bt_size(block) <= min_block_size) {
        min_block_size = bt_size(block);
        min_block = block;
      }
      block = get_next_free_ptr(block);
    }
    if (min_block)
      return min_block;
  }
  return block;
}
#endif

void *malloc(size_t size) {
  // size do ALIGMENT
  size = blksz(size);
  // szukamy bloku
  word_t *block = find_fit(size);

  // jezeli NULL to nie znalezlismy bloku
  if (block == NULL) {
    // robimy morecore(size)
    block = morecore(size);
    // ustawiamy lasta
    last = block;
    // odpowiednio flage prev_Free
    if (bt_free(last))
      bt_set_prevfree(block);

    // optymalizacja pod binarne jezeli size <= 256 to tworzymy bloki za nim
    // tego samego rozmairu
    if (size <= 256) {
      word_t *tmp;
      for (int i = 0; i < 7; i++) {
        tmp = morecore(size);
        bt_make(tmp, size, FREE);
        add_on_class_list(tmp);
      }
      last = tmp;
    }

  } else { // znalezlismy blok

    size_t block_size = bt_size(block);

    // ustawiamy go z listy wolnych blokow
    del_from_class_list(block);

    // jezeli mozemy go rozdzielic na dwa bloki
    if (block_size - size > ALIGNMENT) {

      // to tutaj rozdzielamy czesc ktora zostanie i ustawiamy mu free
      // oraz dodajemy do listy wolnych blokow
      // oraz ustawiamy odpowiednio lasta
      bt_make((void *)block + size, block_size - size, FREE);

      add_on_class_list((void *)block + size);

      if (block == last)
        last = (void *)block + size;

    } else {
      // w przeciwnym wypadku clear'ujemy flage prev_free
      size = block_size;
      bt_clr_prevfree(bt_next(block));
    }
  }
  // ustawiamy blok na used
  bt_make(block, size, USED);

  // zwracamy payload
  return bt_payload(block);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  // jezeli podany zly pointer to odrzucamy
  if (!ptr) {
    return;
  }

  word_t *block = bt_fromptr(ptr);
  word_t *next = bt_next(block);
  size_t block_size = bt_size(block);

  // jezeli nastepny blok jest wolny
  if (bt_free(next)) {
    // usuwamy go z lsity wolnych blokow
    del_from_class_list(next);
    // zmieniamy odpowiednio zmienna size zeby pozniej zlaczyc go
    block_size += bt_size(next);
    // jezeli next == last to ustawiamy lasta
    if (next == last)
      last = block;
  }

  // jezeli poprzedni jest wolny
  if (bt_get_prevfree(block)) {
    word_t *prev = bt_prev(block);
    // usuwamy go z listy wolnych blokow
    del_from_class_list(prev);
    // zmieniamy odpowiednio zmienne zeby pozniej zlaczyc go
    block_size += bt_size(prev);
    if (block == last)
      last = prev;
    block = prev;
  }
  // i laczymy je
  bt_make(block, block_size, FREE);
  add_on_class_list(block);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  // jeżeli podano nulla -> robimy malloc size
  if (!old_ptr)
    return malloc(size);

  // jeżeli podano size = 0 -> robimy free
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  // pobieramy stary block
  word_t *old_block = bt_fromptr(old_ptr);
  size_t old_size = bt_size(old_block);

  // jezeli musimy zmniejszyc rozmiar np blok ma 64 a uzytkownik chce 32
  if (old_size >= size + sizeof(word_t)) {
    size = blksz(size);
    if (old_size == size)
      return old_ptr;

    // rozłączamy blok na dwie części i dodajemy drugą do listy wolnych bloków
    bt_make(old_block, size, USED);
    bt_make((void *)old_block + size, old_size - size, FREE);
    add_on_class_list((void *)old_block + size);

    if (old_block == last)
      last = (void *)old_block + size;

    return old_ptr;
  }

  // jeżeli blok który chcemy zwiększyć to ostatni blok -> optymalizacja
  if (last == old_block) {
    size = blksz(size);
    // liczymy ile musimy dołożyć pamięci
    size_t leftSize = size - old_size;
    // dokładdamy tylko tyle ile potrzebne
    (void)morecore(leftSize);
    // i ustawiamy blok odpowiednie flagi
    bt_make(old_block, size, USED);
    return old_ptr;
  }

  // inaczej mallocujemy nowy blok z sizem
  void *new_ptr = malloc(size);
  if (!new_ptr)
    return NULL;

  // i kopiujemy go całego
  if (size < old_size - sizeof(word_t))
    old_size = size;

  memcpy(new_ptr, old_ptr, old_size);

  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  word_t *block;
  if (verbose)
    msg("CHECKHEAP\n");
  // przechodzimy po kazdym bloku
  for (int class_index = 0; class_index < CLASSES; class_index++) {
    block = class_table[class_index];
    if (verbose)
      msg("[%d] ", class_index);
    while (block) {
      if (verbose)
        msg("%p/%ld : ", block, bt_size(block));
      // size > 0
      assert(bt_size(block) > 0);
      // kazdy blok musi być pomiedzy fajnymi
      assert((void *)block >= mem_heap_lo() && (void *)block <= mem_heap_hi());
      block = get_next_free_ptr(block);
    }
    if (verbose)
      msg("\n");
  }
}
