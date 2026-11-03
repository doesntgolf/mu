let f = fun(x) -> @wrap(x) in f(#a, using {.wrap = fun(y) -> {y}})
