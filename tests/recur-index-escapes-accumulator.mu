recur (l <- &#nil, prev = #none) do prev [#some(p) -> continue(p, prev), #none -> l [#cons(_, t) -> continue(t, #some(t)), #nil -> {}]]
