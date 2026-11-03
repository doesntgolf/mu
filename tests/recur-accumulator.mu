let xs = the (rec 'l. [#nil, #cons('a, 'l)]) &#cons(#a, &#cons(#b, &#nil)) in recur (l <- xs, last = #none) do l [#nil -> last, #cons(x, t) -> continue(t, #some(x))]
