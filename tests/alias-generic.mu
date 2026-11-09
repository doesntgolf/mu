; Each use of an alias has its own type variables
type Id = fun('a) -> 'a in
let f = the Id fun(x) -> x in
let g = the Id fun(y) -> y in
{f(#a), g({})}
