; Eliminating a hole gives a hole, but binding one to a variable or record
; pattern does not
let {a, b} = _ in {_.x, _(#a), {.a = _, .._}, a, #c}
