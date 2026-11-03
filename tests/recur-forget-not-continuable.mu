recur (l <- &#cons(#a, &#nil)) do l [#nil -> {}, #cons(_, t) -> continue(forget(t))]
