let append(xs, ys) = recur (l <- xs) do l [#nil -> ys, #cons(x, t) -> &#cons(x, continue(t))] in append(&#cons(#a, &#nil), &#cons(#b, &#nil))
