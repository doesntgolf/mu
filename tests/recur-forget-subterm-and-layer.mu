recur (l <- &#cons(#a, &#nil)) do let f = forget in l [#nil -> #n, #cons(_, t) -> {continue(t), f(t), f(&l)}.1]
