let val f = fn x => x = x in
  if (f 1) then (f (fn x=> x+1)) else (f (fn x => x))
end
