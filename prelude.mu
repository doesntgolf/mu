; z-combinator
let fix(f) =
	let g(&self) = fun(x) ->
		f(self(&self))(x)
	in
	g(&g)
in

let recur(init, f) =
	let go = fix(fun(self) -> fun(acc) -> f(acc, .continue=self)) in
	go(init)
in

{.fix=fix, .recur=recur}
