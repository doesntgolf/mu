let f() = abstract t in abstract u in {.a = the t #a, .b = the u #b} in let g() = abstract t in abstract u in {.b = the u #a, .a = the t #b} in #c [#c -> f, #d -> g]
