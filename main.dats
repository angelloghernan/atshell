#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "file.sats"
staload "prelude/basics_dyn.sats"
staload "split_string.sats"
staload "./vector.sats"
staload _ = "./vector.dats"
staload "exec.sats"

macdef NULL = $extval(ptr(0), "0")

// abst@ype slice_ptr(a: t@ype, l: addr, n: int) = ptr(l + n * sizeof<a>)

extern fn free_array {a: t@ype}{l: addr}{n: nat}
       (malloced_ptr(l), array_v(a, l, n) | ptr l): void = "mac#free"

extern fn get_line_raw: (&ptr(0) >> ptr l, &size_t? >> size_t, file_t) ->
                        #[l: agz]#[n: pos](malloced_buffer(l), (@[asciiChar][n]) @ l | size_t n) = "mac#getline"

extern fn put_buf {l: addr}{n: int}{a: t@ype} (Buffer(a, l, n)): void = "mac#free"

extern fn fork (): int = "mac#fork"

extern fn execvp_raw {n: int}(string, &(@[string][n])): int = "mac#execvp"

macdef stdin_raw = $extval(file_t, "stdin")

typedef Token(n: int) = [m, k: nat | m <= k | k <= n] @{ str_start=size_t m, str_end=size_t k }

fun {a: t@ype} vector_push {l: agz}{m: pos}{n: nat | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l2, n + 1, k), elem: a):
    #[k: pos | k >= n + 1] #[l2: agz] void = 
    if vec.size < vec.capacity then vector_push_one (vec, elem)
    else let
        val () = vector_expand<a>(vec)
    in
        vector_push_one (vec, elem)
end

fn get_line (): [l: agz][n: pos](Array(asciiChar, l, n)) =
    let
        var p: ptr = NULL
        var allocated_size: size_t
        val (pf1, pf2 | bufsize) = get_line_raw (p, allocated_size, stdin_raw)
    in
        @{ size=bufsize, buffer=((pf1, pf2) | p) }
end

// fn exec () {n: int}


fn array_iter_over {l: addr}{n, i, j: nat | i <= j | j <= n}
                   (array: !Array(asciiChar, l, n), i: size_t i, j: size_t j, f: char -> void): void =
    let
        fun loop {l: addr}{n, i, j: nat | i <= j | j <= n} .<j - i>.
            (buf: !Buffer(asciiChar, l, n), i: size_t i, j: size_t j, f: char -> void): void =
            if i = j then ()
            else let
                val c = array_get_at(!(buf.1), i)
                val () = f (c)
            in loop (buf, i + 1, j, f)
        end
    in
        loop (array.buffer, i, j, f)
end 

fn array_iter {l: addr}{n: nat} (array: !Array(asciiChar, l, n), f: char -> void): void =
    array_iter_over (array, i2sz(0), array.size, f)


fn find_cmd {l: addr}{n: nat}{i: nat | i <= n}
            (array: !Array(asciiChar, l, n), res: &Token(n)? >> opt(Token(n), b), i: size_t i): #[b:bool] bool(b) =
    let
        fun loop {l: addr}{n, i: nat | i <= n} .<n - i>.
            (array: !Array(asciiChar, l, n), i: size_t i): [j: nat | j <= n | j >= i] size_t j =
            if i = array.size then i
            else if array_get_at (!(array.buffer.1), i) = ' ' then i
            else loop (array, i + 1)

        fun first_non_space {l: addr}{n, i: nat | i <= n} .<n - i>.
            (array: !Array(asciiChar, l, n), i: size_t i): [j: nat | j <= n | j >= i] size_t j =
            if i = array.size then i
            else if array_get_at (!(array.buffer.1), i) != ' ' then i
            else first_non_space (array, i + 1)
        
        val start = first_non_space (array, i)
    in
        if start = array.size then false where {
            prval () = opt_none(res)
        }
        else true where {
            // I have no idea why, but I have to explicitly annotate this type
            val str_end: [p: nat | p <= n] size_t(p) = loop(array, start + 1)
            val () = res := @{ str_start=start, str_end=str_end }
            prval () = opt_some(res)
        }
end

fn make_empty_cmd {l: addr}{n: nat} (array: !Array(asciiChar, l, n)): (Token(n)?) =
    res where { var res: Token(n) }

fn make_cmd_vec {l: addr}{n: nat} (array: !Array(asciiChar, l, n)): [l2: agz](Vector(Token(n), l2, 0, 1)) =
    res where { var res = vector_make<Token(n)> () }

fn print_maybe_cmd {l: addr}{n: nat}{b: bool}
             (array: !Array(asciiChar, l, n), maybe_cmd: !opt(Token(n), b), b: bool b): void =
    if b then let
        prval () = opt_unsome (maybe_cmd)
        val () = array_iter_over (array, maybe_cmd.str_start, maybe_cmd.str_end, lam c => print (c))
        prval () = opt_some (maybe_cmd)
    in end
    else ()

fn print_cmd {l: addr}{n: nat}{b: bool}
             (array: !Array(asciiChar, l, n), cmd: Token(n)): void = () where {
    val () = array_iter_over (array, cmd.str_start, cmd.str_end, lam c => print (c))
}

fn print_cmds {l: addr}{n: nat}{l2: agz}{k: pos}{m: nat | m <= k}
    (array: !Array(asciiChar, l, n), cmds: !Vector(Token(n), l2, m, k)): void = () where {

    fun loop{l: addr}{n: nat}{l2: agz}{k: pos}{m: nat | m <= k}{i: nat | i <= m}
        (array: !Array(asciiChar, l, n), cmds: !Vector(Token(n), l2, m, k), i: int i): void =
        if i2sz(i) = cmds.size then ()
        else let
            val cmd = vector_get (cmds, i)
            val () = array_iter_over (array, cmd.str_start, cmd.str_end, lam c => print (c))
        in
            loop (array, cmds, i + 1)
        end

    val () = loop (array, cmds, 0)
}


fn parse_cmds {l: addr}{n: nat}{l2: agz}
              (array: !Array(asciiChar, l, n), vec: &Vector(Token(n), l2, 0, 1) >> Vector(Token(n), l3, m, k)): 
              #[l3: agz]#[k: pos]#[m: nat | m <= k] void =
    let
        fun loop {l: addr}{l2: agz}{k: pos}{n, m, i: nat | i <= n | m <= k} 
                 (array: !Array(asciiChar, l, n), 
                  vec: &Vector(Token(n), l2, m, k) >> Vector(Token(n), l3, m2, k2), 
                  i: size_t i): #[l3: agz] #[k2: pos] #[m2: nat | m2 <= k2] void =
            if i = array.size then ()
            else let
                var maybe_cmd = make_empty_cmd (array)
                val b = find_cmd (array, maybe_cmd, i)
            in
                if b then let
                    prval () = opt_unsome (maybe_cmd)
                    val () = vector_push<Token(n)>(vec, maybe_cmd)
                in 
                    loop(array, vec, maybe_cmd.str_end)
                end
                else let 
                    prval () = opt_unnone (maybe_cmd)
                in end
            end
    in
        loop (array, vec, i2sz(0))
    end
    

implement main0 (argv, argc) = 
    let
        val () = print ("> ")

        val array = get_line ()

        val () = println! ("Array size is ", array.size)
        val () = array_iter_over (array, i2sz(0), array.size, lam c => print c)

        var split = array_to_split_string (array.buffer.0, array.buffer.1, array.size, ' ')

        val term = make_terminated (split, array.buffer.1)

        val ret = exec_variable_params (term)

        prval av = terminated_array_v_to_array_v (term.tpf)

        val () = free_array (term.mpf, av | term.p)

        prval buf_v = split_string_v_to_buffer_v (split.pf, split.str_view)

        val () = array.buffer.0 := buf_v

        val () = array_iter_over (array, i2sz(0), array.size, lam c => (if c = '\0' then print "0" else print c))

        var cmds = make_cmd_vec (array)

        val () = parse_cmds (array, cmds)

        // val () = print_cmds (array, cmds)

        val () = dynarray_dealloc (cmds.detail)

        val () = put_buf (array.buffer)
    in
end
