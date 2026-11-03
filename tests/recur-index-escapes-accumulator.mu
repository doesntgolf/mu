recur go(l <- &#nil, prev = #none) -> prev [#some(p) -> go(p, prev), #none -> l [#cons(_, t) -> go(t, #some(t)), #nil -> {}]]
