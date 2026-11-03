recur (l <- &#cons(#a, &#cons(#b, &#cons(#c, &#nil)))) do l [#nil -> #none, #cons(x, t) -> x [#b -> #some(t), _ -> continue(t)]]
