#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

absview malloced_buffer(addr)

stadef REPLACEMENT_CHAR = 26
typedef validChar = [c: int | c > 0 | c != REPLACEMENT_CHAR] char(c)

typedef asciiChar = [c: int | c >= 32 | c <= 126] char(c)

// address, size, num strings (C strings)
dataview split_string_v(l: addr, int, int) =
  | split_string_end (l, 0, 0) of ()

  | {n: nat}{m: nat}
    split_string_nil (l, n + 1, m + 1) of (char(0) @ l, split_string_v(l + sizeof(char), n, m))

  | {n: nat}{m: nat}
    split_string_replace (l, n + 1, m) of (char(26) @ l, split_string_v(l + sizeof(char), n, m))

  | {n: nat}{m: nat}
    split_string_cons (l, n + 1, m) of (asciiChar @ l, split_string_v(l + sizeof(char), n, m))

viewdef BufferView(a: t@ype, l: addr, n: int) = (malloced_buffer(l), (@[a][n]) @ l)

vtypedef Buffer(a: t@ype, l: addr, n: int) = (BufferView(a, l, n) | ptr l)

vtypedef Array(a: t@ype, l: addr, m: int) = @{ size=size_t m, buffer=Buffer(a, l, m) }

vtypedef SplitString(l: addr, n: int, m: int) =
  @{ size=size_t n, num_strings=size_t m, str_view=split_string_v(l, n, m), pf=malloced_buffer(l) }

praxi split_string_v_to_buffer_v {l: addr} {n: nat} {m: nat}
      (malloced_buffer(l), split_string_v(l, n, m)): BufferView(asciiChar, l, n)

praxi split_string_v_is_end {l: addr} {m: nat}
      (!split_string_v(l, 0, m)): [m == 0] void

praxi split_string_v_n_is_not_end {l: addr}{n: pos}{m: nat}
      (!split_string_v(l, n, m)): [m > 0] void

praxi split_string_v_m_is_not_end {l: addr}{n: nat}{m: pos}
      (!split_string_v(l, n, m)): [n > 0] void

typedef undeterminedChar(m: int, m2: int) = 
  [c: int | (c == 0 && m2 == m - 1) || (c == 26 && m2 == m) || ((c >= 32 && c <= 126) && m2 == m)]
  char(c)

praxi split_string_get_first {l: addr} {m, n: pos}
      (split_string_v(l, n, m)): 
      [mm: nat | mm == m || mm == m - 1]
      (undeterminedChar(m, mm) @ l, split_string_v(l + sizeof(char), n - 1, mm))

fn array_to_split_string {l: addr} {n: pos}
   (buf_view: BufferView(asciiChar, l, n), p: ptr l, size: size_t n, delimiter: asciiChar): [m: nat] SplitString(l, n, m)
