%{^
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <string.h>
#include <unistd.h>
%}

%{^
typedef struct { char pad[128]; } padding;
%}

extern fun po2(s:uint): uint = "mac#"
extern fun bitwise_and_uint(uint, uint): uint = "mac#"
extern fun ipc_comp_barrier(): void = "mac#"
extern fun ipc_write_barrier(): void = "mac#"
extern fun ipc_relax(): void = "mac#"

%{
#define force_inline __attribute__ ((__always_inline__))

static unsigned int po2(const unsigned int size)
{
  unsigned int i;
  for (i=0; (1U << i) < size; i++);
  return 1U << i;
}

static inline unsigned int force_inline bitwise_and_uint(const unsigned int x, const unsigned int y)
{
  return x & y;
}

static inline void force_inline ipc_comp_barrier() { asm volatile("":::"memory"); }

static inline void force_inline ipc_write_barrier() { asm volatile("sfence":::"memory"); }

static inline void force_inline ipc_relax()  { asm volatile ("pause":::"memory"); } 
%}

extern fun open(string, int, int): int = "mac#"
extern fun ftruncate(int, size_t): int = "mac#"
extern fun mmap(ptr, size_t, int, int, int, int): ptr = "mac#"
extern fun memset(ptr, int, size_t): ptr = "mac#"

typedef statbuf = $extype_struct "struct stat" of {
  st_size = size_t
}

extern fn fstat(int, ptr): int = "mac#"
