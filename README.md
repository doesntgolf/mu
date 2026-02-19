# μ programming language

Mu is a small, high-level, pure functional programming language with an ML-style type
system. Its design is focused on anonymous types, inference, and polymorphism.

Starting from a Hindley-Milner type system with let-polymorphism, we add:

 - product and sum types with row polymorphism
 - row polymorphic function parameters
 - existential types
 - iso-recursive types
 - a denominator-polymorphic number type, with units of measure
 - pattern matching with sub-clauses

**Design status:** The main design for the type system and language semantics that
I'd like is in place, though some things still need to be fleshed out. Inconsistencies
and deficiencies will probably still be uncovered during implementation. The syntax
is still mostly undesigned.

**Implementation status:** I'm implementing the bootstrapping type checker and
tree-walk interpreter in OCaml. It's still in the beginning stages, not yet usable for
anything. Concurrently with that, I'm designing a minimal prelude, to expose builtins
and basic data structures and utilities. After that, I plan to implement a bytecode
interpreter and runtime in C, and a self-hosted type-checker and compiler targeting
that bytecode. At some point, I also intend to write a specification for the language.

## Type system

### Denominator polymorphism and units of measure

Mu's number type represents rational numbers, where the denominator is part of the type.
The denominator is a monomial: it's represented by the product of a coefficient and a set
of variables. So the literal `5` has type `Num/1a` - that is, a number with denominator
1 multiplied by the variable `a`. The decimal literal `12.3` has type `Num/10a`. The
`a` is a numeric type variable, freshly allocated for each literal value. Its purpose
is similar to a row variable in a record type: it makes the value flexible. A `Num/4a`
can be unified with a `Num/6b` by setting `a = 3` and `b = 2`. By contrast, a number
type without any variables in the denominator is inflexible - an indexing operation
should require a `Num/1`. In general, the unifier unifies denominators by finding the
least common multiple of the coefficients.

A number without a statically known denominator is notated `Num/?`. This type can
be unified with another `Num/?`, or with any number whose denominator has a free
type variable in it (by setting that variable equal to `?`, the whole denominator
becomes `?`). The types `Num/1` and `Num/?` cannot be unified. Operations on values of
type `Num/?` will still be mathematically correct, we just won't know the resulting
denominator until runtime. A number with a statically unknown denominator can be turned
into one with a statically known denominator with functions like `quantize` or `floor`.

Addition, subtraction, equality, and comparison demand operands with compatible
denominators. Multiplication has type `fun(Num/a, Num/b) -> Num/a*b`, combining the
two denominators. The type for division (`fun(Num a/b, Num c/d) -> Num/b*c`) shows
another feature of number types: numerators in the type.

The numerator is part of a number type in one specific circumstance: number literals. So,
the type of the literal `5` is actually `Num 5/1a`. The purpose of having the numerator
in the type is for a few operations (division, exponentiation, quantization) where
the denominator of the output type depends on the numerator of one of the operands;
this way, if you divide by a number literal (as is the common case), we're able to
preserve a statically known denominator in the output. Across any operation, the known
numerator component is immediately forgotten.

Finally, units of measure can also be attached to numbers. There are no builtin units;
a unit is simply any string raised to an exponent. Thus, you can have `3.6 meters`,
`5 apples`, `80 miles/hour`, or `40 m^3`. Units compose and cancel out as
you would expect across multiplication and division; addition and comparison require
alike units.

### Existential types

In the HM type system, quantifiers for universal type variables aren't part of types
themselves; instead they occur in so-called "prenex form". They're generalized at
`let` (and at the implicit "top-level `let`"), and instantiated at variable usage
sites. Similarly, in the Mu type system, existential quantifiers aren't types themselves,
they're a component of function types. Existential type variables are instantiated
by the introduction form (`exists T in <body>`), generalized at function boundaries,
and re-instantiated at every function application.

The introduction expression for existential types is `exists <T> in <body>`.  Within
`<body>`, `<T>` is used as a constructor expression and pattern, essentially annotating
occurrences of the abstract type-to-be. After `<body>`, a fresh existential type variable
is allocated for the abstract type, which unifies with nothing but itself. Then,
when inferring the type for a function, when we see an existential type variable, we check
if it occurs in the environment of the function; if so, it remains a simple
constant. If not, it means that variable was introduced within the function,
and the existential quantifier for that variable thus becomes part of the function type.
This mirrors the environment check for generalization of universal type variables at
`let`. (And likewise, the environment check can be optimized by tracking the "level"
or "rank" of the respective type variables - `let` depth for universal type variables,
and function depth for existential type variables.)

At every function application, the existential quantifiers associated with the
function type are instantiated, assigning new, unique type variables for each
quantifier. Instead of being bound to the unpack scope, as in the Mitchell-Plotkin
formulation, the existential quantifier naturally flows outward with the occurrence
of the associated type variable.

### Explicit iso-recursive types, corresponding with lazy evaluation

In the type system literature for iso-recursive types, explicit `roll e` and `unroll
e` expressions are used to convert back and forth between a wrapped form like `rec
nat. [Succ(nat), Zero]`, and the one-level-unwrapping `[Succ(rec nat. [Succ(nat),
Zero]), Zero]`. The two forms are isomorphic.

But in most languages that have iso-recursive types, the roll and unroll operations
are made implicit in the data constructors of the language. For example, in OCaml we
would write the previous example `type nat = Zero | Succ of nat`.  Constructing it
in an expression or pattern with `Succ Zero` implicitly performs the roll or unroll,
respectively.

But Mu, with its anonymous types, isn't able to infer the roll and unroll forms as
easily. (So perhaps we should instead use equi-recursive types, where the rolled and
unrolled form are treated as equal to each other, rather than isomorphic?  Unfortunately,
inferring equi-recursive types is a much harder job. Stephan Dolan's language MLsub
does it, but the MLsub type system has a very different design, based on subtyping,
than Mu.) So instead, we make roll explicit in the surface language, with the syntax
`&e`. Unrolling is simply using the same syntax in a pattern, `&p`.

Normally, the explicit roll requires a type annotation, otherwise it's unclear where
the fold in the recursive structure should be placed. Instead, we use another sigil.
Within a `&body` expression or pattern, `body` can contain 0 or more `^e` forms (I
pronounce it "pin"). The "pinned" expression (or pattern) marks the folding point in
the recursive type, constraining that sub-expression to match the type of the parent
recursive structure.

Mu is strictly evaluated, but we also have opt-in laziness, serendipitously corresponding
with recursive types. A `&e` expression becomes a lazy thunk. Pattern matching on a
lazy thunk with `&p` forces it. Notably, an iso-recursive type need not be actually
recursive, so you can put this to use for lazy evaluation wherever you want it.

Recursive types are also useful for existentials. Because roll expressions - like
functions - are delayed, rolls generalize existential types and unrolls instantiate
them, just like function abstraction and application. Recursive types therefore also
carry existential type quantifiers. This provides a straightforward way to make two
types containing different existential variables compatible with each other:

```
let &shape = if cond then
	exists T in &{
		.data = T({.radius = 2.0}),
		.area = fun(T(circ)) -> pi * circ.radius * circ.radius
	}
else
	exists T in &{
		.data = T({width = 1.8, height = 1.2}),
		.area = fun(T(rect)) -> rect.width * rect.height
	}
```

If we didn't have the rolls in each branch, the type of each branch would be `{.data :
~t, .area : fun(~t) -> Num}`, except that each branch has its own, unique `~t`. The type
checker will find the `~t` from one side incompatible with the `~t` from the other,
and thus reject the expression. But with the rolls, the type of each branch becomes
`& exists ~t. {.data : ~t, .area : fun(~t) -> Num}`. With the existential quantifier
in place, the types of the two branches are compatible. Outside the conditional,
we immediately unpack with the roll pattern in `let &shape = ...`, instantiating the
existential variable.

#### No recursive bindings

Mu has purely lexical scope, with no recursive bindings. Thanks to iso-recursive types,
we can type the Z-combinator, which we've placed in the prelude. With that, we
derive a function called `recur` (based loosely on Clojure's `loop/recur` form), also
in the prelude. `recur` is meant to be the primary way to do recursion in the language.

### Arrays

Arrays have their size as part of their type when it's statically known. When it's not
statically known, or when two arrays with different sizes are unified, the resulting
type has `?` for the size. Functions like `Array.map` are polymorphic over the array
size. Functions like `Array.init` (with type `fun(Num 'a/1, fun(Num/1) -> 'b) ->
Array<'b, size='a>`) can make use of integers of static information from a number type to retain
static information about array size.

Strings are likewise arrays of bytes. The prelude will also contain an existential
type for UTF8 strings.

### Pattern matching sub-clauses

In a match expression, a clause is normally `<pat> -> <expr>`. Sub-clauses allow the
form `<pat> and <expr> [<pat> -> <expr> ..]`. That is, you can do an inner match on an
arbitrary scrutinee using parts you've matched from the outer pattern.  Crucially,
the sub-clause matching may be partial - if there's no match in the sub-clause,
control flows back out to the outer clause.

This generalizes boolean guard clauses in other pattern matching implementations. It
also subsumes the need for a pattern like OCaml's `<pat> as x` (where you both match a
specific structure and bind that structure to a variable), and also range patterns like
`1..10` (since you can simply do that test in a sub-clause). An example in OCaml-ish
syntax:

```ocaml
match x with
| A -> 1
| B (5, x) and match f x with
	| 100 -> 2
	| 200 -> 3
end
| C x -> x
| _ -> default
```

### Forall notation

Mu has rank-1 polymorphism, where quantifiers for universal type variables (`forall
a. ...`) are outside the type itself, in a "type scheme". Despite this, in the type
notation we always display the quantifier at the smallest region that contains all of
the variable's occurrences, rather than on the outside. And for universal variables
with one occurrence, we notate it without a quantifier, as `*`. The reason for this
is that, because we lack the module system that many ML-family languages have, we use
records to bundle common functionality into a package. And if that package operates on
generic data structures, the type of each item in the package may end up accruing one
or more universal type variables. When we view the type of that package as a whole, it
may end up looking like `forall a b c d. {.x : a, .f : b -> b, .g : c -> d -> {c, d}}`,
which is arguably not user-friendly. So instead, with the regional quantifier notation,
that type is written `{.x : *, .f : forall a. a -> a, .g : forall a b. a -> b -> {a, b}}`.

### Comprehensions

```
mod {
	bind x, y = f(z) in
	let a = g(x, y) in
	where a < b
	yield a
}
```

desugars to

```
mod.bind(f(z), fun(x, y) ->
	let a = g(x, y) in
	if a < b then
		mod.unit(a)
	else
		mod.zero)
```

Type inference works just as it would for the desugared version. (If you don't use
`bind`, `yield`, or `where`, then `mod` doesn't need to have `bind`, `unit`, or
`zero` respectively.)

(**TODO**: flesh out this design more. I think this is overall most similar to F#'s
computation expressions?)

### Dependencies

#### Function dependencies

Sometimes a function may work on a generic type of data, but it may depend on certain
functionality associated with the type, like an `equal` or `add` function. In Haskell and
Rust, typeclasses and traits are used to accomplish this. In OCaml, we may use functors
(like `Set.Make`) or normal arguments (like the first argument to `List.equal`).
In Mu, we use dependencies. Every function takes a dependency argument, which is
always a record. In the body of the function, you can use the form `@<label>`, as in
`@compare(a, b)`, or `@mul(x, y)`. The type of the dependency parameter is inferred
via normal type inference. In the application form, the dependency is specified as the
last argument, with the keyword `using`, as in `f(a, b, using c)`. Not including the
dependency argument is the same as passing an empty record.

#### Package dependencies

The `@<label>` form can also be used at the top level of a file, for inter-package
dependencies.  One package can't directly reference another - instead, an external package
manifest composes packages, passing dependencies as necessary. The manifest references
packages via their cryptographic hash. Registries are mappings from a petname to the
hash representing a package. File trees form a local registry with file paths as petnames.

### Variants, records, and functions

Variants (written `'ok(a, b)` or `'true`) are row polymorphic, similar to OCaml's
polymorphic variants. A variant type is written `['one, 'two(['three, 'four]), 'five,
..rest]`, with the `..rest` denoting the row variable.

Rather than a separate construct for tuples, records can begin with 0 or more positional
fields. Records are row-polymorphic in the typical form. When records are used in
pattern position, if the row parameter isn't explicitly bound, it's implicitly the
wildcard pattern (NOT the empty row), so there's no way to form a closed record pattern.

Functions are applied with the Algol-form (`f(a, b, c)`), rather than the curried ML-form
(`f a b c`). The primary motivation for this design is so that row-polymorphism can
be applied to function parameters, making more functions type-compatible with each
other.

## Todo

### Design

 - Syntax
 - Prelude
 - Terminology (currently using packages to mean "something with an existential type", and
   also a "file")
 - Metaprogramming? (maybe type-safe eval as in https://haskellforall.com/2026/01/typesafe-eval
   except taking an AST (and environment?) rather than a string)

### Implementation

 - Bootstrap parser, typechecker, tree walking interpreter (in progress)
 - Write "Learn Mu in 15 minutes"
 - Type system specification (maybe in Rocq)
 - Bytecode interpreter and runtime, and a compiler targeting it

## Design philosophy

### Why design for complete type inference?

I don't see full type inference as an end in itself, though it is nice. Instead, I see
having a predictable language semantics and type system as the goal, and complete type
inference via a simple algorithm as a signpost pointing toward that goal.
