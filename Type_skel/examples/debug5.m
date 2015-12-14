let val f = fn x => x = x in
  if (f 1) then (f 5) else (f (fn x => x))
end
