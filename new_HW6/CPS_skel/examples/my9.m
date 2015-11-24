(rec s x => ifzero x then 0 else (x + (s (x + (-1))))) ((((fn z => ifzero ((fn x => x + 1) z) then 1 else z) 5, (fn z => ifzero ((fn x => x + 1) z) then (z+1) else 2) (-1)).1))

