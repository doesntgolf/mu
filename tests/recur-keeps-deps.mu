let f(xs) = recur go(l <- xs) -> l [#nil -> @z, #cons(_, t) -> go(t)] in f(&#cons(#a, &#nil), using {.z = #z})
