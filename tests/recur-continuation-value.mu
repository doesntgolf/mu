recur (l <- &#cons(#a, &#nil)) do l [#nil -> #nil, #cons(x, t) -> let f = continue in f(t)]
