recur go(l <- &#cons(#a, &#cons(#b, &#nil))) -> l [#nil -> &#done, #cons(_, t) -> &#more(fun() -> go(t))]
