let mod = abstract T in {.make(x) = the T x, .unwrap(the T x) = x} in let x = mod.make(#a) in let y = mod.make({}) in #c [#c -> x, #d -> y]
