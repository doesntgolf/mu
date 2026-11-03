let len(xs) = recur (l <- xs) do l [#nil -> &#z, #cons(_, t) -> &#s(continue(t))] in recur (l <- &#cons({}, &#nil)) do l [#nil -> #done, #cons(_, t) -> len(t) [_ -> continue(t)]]
