(fn z => ((fn x => ifzero ((fn x => x - 2) (z)) then (x.1) else (x.2)) (5, 3))) 2 
