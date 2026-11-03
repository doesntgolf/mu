recur (l <- &#cons(#a, &#cons(#b, &#nil))) do l [#nil -> &#done, #cons(_, t) -> &#more(fun() -> continue(t))]
