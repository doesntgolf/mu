let len(xs) = recur go(l <- xs) -> l [#nil -> &#z, #cons(_, t) -> &#s(go(t))] in recur go(l <- &#cons({}, &#nil)) -> l [#nil -> #done, #cons(_, t) -> len(t) [_ -> go(t)]]
