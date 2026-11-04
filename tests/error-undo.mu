; Errors are undone, so f keeps its type
let f(x) = x [#a -> #b] in {f(#c), f(#a)(#d)}
