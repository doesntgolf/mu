fun(xs) -> recur (l <- xs) do l [#nil -> #nil, #cons(_, t) -> continue(t)]
