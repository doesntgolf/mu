let mk() = abstract T in {.make(x) = the T x, .unwrap(the T x) = x} in let m = mk() in {m.make(#a), m.unwrap(m.make({}))}
