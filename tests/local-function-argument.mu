; Arguments are checked against the parameters, in order, so the one that
; disagrees with the others is blamed, not the application
let apply(f, x) = f(x) in apply(fun(y) -> y [#a -> #b], #c)
