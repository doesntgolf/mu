recur go(l <- &#cons(#a, &#nil)) -> l [#nil -> #nil, #cons(x, t) -> let f = go in f(t)]
