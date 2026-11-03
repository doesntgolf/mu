let append(xs, ys) = recur go(l <- xs) -> l [#nil -> ys, #cons(x, t) -> &#cons(x, go(t))] in append(&#cons(#a, &#nil), &#cons(#b, &#nil))
