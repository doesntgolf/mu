recur (l <- &#nil, prev = #none) do abstract s in prev [#some(the s p) -> continue(p, prev), #none -> l [#cons(_, t) -> continue(t, #some(the s t)), #nil -> {}]]
