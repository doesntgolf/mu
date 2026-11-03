let f(xs) = recur (l <- xs) do l [#nil -> @z, #cons(_, t) -> continue(t)] in f(&#cons(#a, &#nil), using {.z = #z})
