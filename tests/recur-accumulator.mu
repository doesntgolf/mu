let xs = the (rec 'l. [#nil, #cons('a, 'l)]) &#cons(#a, &#cons(#b, &#nil)) in recur go(l <- xs, last = #none) -> l [#nil -> last, #cons(x, t) -> go(t, #some(x))]
