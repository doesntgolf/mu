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

let num = {
	; `$name` syntax is for builtins, only available to the prelude
	.add(a, b) = $add(a, b),
	.mul(a, b) = $mul(a, b)

	;; IDEA: parse(str, base, denom)
}
in

let list = {
	.map(xs, f) =
		recur(xs, fun(tl, .continue) ->
			&(tl [
				&#cons(hd, ^tl) ->
					let hd = f(hd) in
					#cons(hd, continue(tl)),
				&_ ->
					#nil
			]))
}
in

let map({.compare}) =
	exists T in {
		.empty = T(#nil)
	}
in

{.fix=fix, .recur=recur}
