let tree = &#node(&#node(&#leaf, &#leaf), &#leaf) in recur size(n <- tree) -> n [#leaf -> &#z, #node(a, b) -> recur add(m <- size(a), acc = size(b)) -> m [#z -> &#s(acc), #s(p) -> &#s(add(p, acc))]]
