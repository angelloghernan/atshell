#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

absview malloced_buffer

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

viewdef BufferView(a: t@ype, l: addr, n: int) = (malloced_buffer, (@[a][n]) @ l)

vtypedef Buffer(a: t@ype, l: addr, n: int) = (BufferView(a, l, n) | ptr l)

vtypedef Array(a: t@ype, l: addr, n: int) = @{ size=size_t n, buffer=Buffer(a, l, n) }

vtypedef SplitString(l: addr, n: int, m: int) =
  @{ size=size_t n, num_strings=size_t m, str_view=split_string_v(l, n, m), pf=malloced_buffer }

praxi split_string_v_to_buffer_v {l: addr} {n: nat} {m: nat}
      (malloced_buffer, split_string_v(l, n, m)): BufferView(char, l, n)

fn array_to_split_string {l: addr} {n: nat}
   (buf_view: BufferView(asciiChar, l, n), p: ptr l, size: size_t n, delimiter: asciiChar): [m: nat] SplitString(l, n, m)
