let m = abstract t in the {.make : fun() -> t, .get : fun(t) -> [#a]} {.make() = #a, .get(x) = x} in m.get(m.make())
