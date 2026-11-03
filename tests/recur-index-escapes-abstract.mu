recur go(l <- &#nil, prev = #none) -> abstract s in prev [#some(the s p) -> go(p, prev), #none -> l [#cons(_, t) -> go(t, #some(the s t)), #nil -> {}]]
