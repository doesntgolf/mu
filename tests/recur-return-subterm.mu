recur go(l <- &#cons(#a, &#cons(#b, &#cons(#c, &#nil)))) -> l [#nil -> #none, #cons(x, t) -> x [#b -> #some(t), _ -> go(t)]]
