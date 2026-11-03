recur outer(l <- &#cons(&#cons(#a, &#nil), &#cons(&#cons(#b, &#nil), &#nil))) -> l [#nil -> &#nil, #cons(xs, t) -> recur inner(m <- xs) -> m [#nil -> outer(t), #cons(x, u) -> &#cons(x, inner(u))]]
