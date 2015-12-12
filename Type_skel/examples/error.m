let val I = malloc (fn x => x) in
  I := (fn x => x + 1);
  (!I) true
end
