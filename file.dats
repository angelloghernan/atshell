staload "file.sats"
#define ATS_DYNLOADFLAG 0

implement file_read1 (pf, fpf | p, sz, fptr) =
    file_read_raw (pf, fpf | p, i2sz(1), sz, fptr)

implement file_read (pf, fpf | p, sz, f) =
          let
              val (pf1, pf2 | ret) = file_read_raw1 (pf, fpf | p, i2sz(1), sz, f)
          in
              (pf1, pf2 | ret)
end

implement file_write {m, n} (fpf | A, sz, f) =
    let
        val ret = $extfcall([o: nat | o <= m] size_t o, 
                            "fwrite", addr@A, 1, sz, f)
    in
        ret
end

implement file_open (file_name, mode) =
          $extfcall([l: addr] (option_v(File(l), l > null) | ptr l), 
                    "fopen", file_name, mode)
