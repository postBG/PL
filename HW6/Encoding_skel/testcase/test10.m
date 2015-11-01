(rec fac x => (ifzero x then 0 else (ifzero (x - 1) then 1 else (fac (x - 2) + fac (x - 1))))) 6
