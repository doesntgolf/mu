# μ programming language and environment

Mu is a small, total, pure functional, ML family programming language. Its
design is focused on anonymous types, inference, and polymorphism.

Starting from a Hindley-Milner type system, we add:

 - anonymous records and variants with row polymorphism
 - generative existential types
 - anonymous, strictly positive iso-recursive types, and an expression
   for structural recursion
 - units of measure (TODO)

The language is paired with and designed for a dedicated editing and evaluation
environment.

**Status:** The language design is still somewhat in flux. The bootstrapping type checker
and interpreter in OCaml is still in the beginning stages. It type checks while parsing,
which keeps the language honest about being checkable in a single pass.

## Type system

### Records, variants, and functions

Record and variant expressions don't need their types to be pre-declared - the types
inferred for their introduction and elimination forms are anonymous and use row
polymorphism for flexibility of the inferred types. Instead of tuples as a separate
construct, records begin with 0 or more positional fields, followed by 0 or more named
fields, as in `{a, b, .x = c}`. Positional fields are labelled from 1, so the fields of
that record are `.1`, `.2` and `.x`. A record can be extended with the fields of another
record, as in `{.x = c, ..r}`; fields given explicitly replace those of `r`, and must have
the same type.

Variant literals are written with a leading `#`, as in `#ok(a, b)` or `#true`. Variant
types are written with square brackets, like `[#one, #two({}, {}), ..'rest]`, with
`..'rest` denoting the row variable. Type variables, row variables included, are written
with a leading apostrophe. The optional payload of a variant is written in parentheses
after the tag, and is itself a record, which can also contain a row variable. Record
types are written like `{'a, .x : 'b, ..'rest}`.

Variants are eliminated by `match`, which is written as a list of clauses after the
scrutinee, as in `x [#some(y) -> y, #none -> d]`. Patterns mirror expressions: variables,
`_`, records (`{p, .x = q}`, or `{.x = q, ..}` to allow other fields), variants, and
alternatives (`p or q`). A match without a catch-all clause gives the scrutinee a closed
variant type, containing only the tags its clauses handle. The prefix forms `&e` and
`the T e` include field accesses and applications in `e`, but not a match, so
`&x [&y -> y]` matches on `&x`.

Functions are written `fun(a, b, .c = d) -> body`, where the parameters are patterns.
They're applied with the Algol-form (`f(a, b, .c = g(x))`), rather than the curried
ML-form (`f a b (g x)`), and - like records - take 0 or more positional parameters,
followed by 0 or more named parameters. Function types are written like
`fun('a, .c : 'b) -> 'c`, and may also end the parameters with a row variable.

Bindings are written `let p = e1 in e2`, where `p` is a pattern. Two forms of sugar
define functions: `let f(x, y) = body in rest` means `let f = fun(x, y) -> body in rest`,
and the record field `{.f(x) = body}` means `{.f = fun(x) -> body}`.

### Explicit iso-recursive types

In the type system literature for iso-recursive types, explicit `roll e` and `unroll
e` expressions are used to convert back and forth between a wrapped form like
`rec 'nat. [#succ('nat), #zero]`, and the one-level-unwrapping
`[#succ(rec 'nat. [#succ('nat), #zero]), #zero]`. The two forms are isomorphic.

But in most languages that have iso-recursive types, the roll and unroll operations
are made implicit in the data constructors of the language. For example, in OCaml we
would write the previous example `type nat = Zero | Succ of nat`.  Constructing it
in an expression or pattern with `Succ n` implicitly performs the roll or unroll,
respectively.

In Mu - because of its focus on anonymous types - the roll is made explicit with the
`&e` form. Unrolling is using the same form in a pattern. There are typically difficulties
inferring recursive types with an explicit roll, because of ambiguity with where the
roll in the resulting type should be placed. Instead, a roll on its own doesn't infer a
recursive type. Because of our focus on anonymous types, the two types
`rec 'l. [#cons('l), #nil]` and `rec _. [#cons(rec _. [#nil, ..'a]), ..'b]` are
compatible, so for `&#cons(&#nil)` we simply infer the latter. An actual recursive type
comes from a type annotation, as in `the (rec 'l. [#cons('l), #nil]) &#cons(&#nil)`, or
is inferred for the input of a `recur` expression (below).

Recursive types must be strictly positive: in an annotation, the recursive variable may
not occur within a function's parameter types. Recursion can't be introduced any other
way - for example, applying an unrolled function to its own rolled form, as the Y
combinator does, fails the occurs check of unification.

### Recursion

Mu has purely lexical scope, with no recursive bindings. And because recursive types
are restricted to strictly positive form, expressions like the Y combinator that
introduce general recursion (and divergence) are type errors. Instead, Mu includes a
`recur` expression for structural recursion, where recursive applications must be made
on subterms of the current input.

There are a few different systems for enforcing that recursion happens on subterms.
Maybe the simplest is doing a syntactic check on the recursive call, but this suffers
from not being compositional in the way a type-based mechanism is. There are size-
based systems, where recursive types are given an index describing size relationships
between each level. These are very expressive, but introduce subtyping to the type
system, rather than using ordinary unification like Mu aims to do. Then there are also
Mendler-style recursion combinators which use rank-2 polymorphic types to give subterms
an abstract type.

Mu's system is based on Mendler-style recursion. But instead of making the recursive type
itself abstract, we add a type index to recursive types, like sized types. But instead of
sizes, the index contains an abstract variable, which may be either present or absent. The
index on a recursive type "at rest" is in the absent state. But within a `recur`
expression, an abstract variable is introduced in the index on the recursive type of the
input data being traversed. When unrolling a recursive type, the child form has the same
type index as the parent; when rolling a new layer onto a recursive type, the index of
the new parent is always in the absent state. There is also a `forget e` expression for
moving from a present abstract type index to the absent state. Type inference and checking
of the type index then uses plain unification.

### Existential types and type annotation

In the HM type system, quantifiers for universal type variables aren't part of types
themselves; instead they occur in so-called "prenex form". They're generalized at
`let` (and at the implicit "top-level `let`"), and instantiated at variable usage
sites. Similarly, in the Mu type system, existential quantifiers aren't types themselves,
they're a component of function types. Existential type variables are instantiated
by the introduction form (`abstract t in <body>`), generalized at function boundaries,
and re-instantiated at function application.

The introduction expression for existential types is `abstract <T> in <body>`. It
allocates a fresh existential type variable for the abstract type, which unifies with
nothing but itself. Within `<body>`, `<T>` may be used in type annotations to refer to
it, and after `<body>` the name is out of scope, so the type is sealed.
Then, when inferring the type for a function, when we see an existential type variable, we check
whether it was introduced within the function, rather than in an enclosing scope. If
not, it remains a simple constant. If so, the existential quantifier for that variable
becomes part of the function type. This mirrors generalization of universal type
variables at `let`, and both are implemented by tracking the "level" of each type
variable - `let` depth for universal type variables, and function depth for existential
type variables. An existential type variable introduced within a function may occur in
its result type, but not in its parameter types.

At every function application, the existential quantifiers associated with the
function type are instantiated, assigning new, unique type variables for each
quantifier. Instead of being bound to the unpack scope, as in the Mitchell-Plotkin
formulation, the existential quantifier naturally flows outward with the occurrence
of the associated type variable.

Mu's type annotations - written `the <type> <expr>` - may be used in either expression
or pattern position, and they actually have a simple typing rule which isn't simply
checking whether the annotated type and the inferred type of the expression match. In
`the ty x`, the whole annotated expression (`the ty x`) is given type `ty`, and the
subexpression `x` is constrained to have type `repr(ty)`. `repr` is a type-level
operation which doesn't occur in the surface level type language. For an abstract type
`t`, `repr(t)` denotes its underlying type, which is inferred from the uses of `t` within
its `abstract` scope. For other types, `repr` goes through the structure of the type,
replacing each abstract type written in it by its underlying type - e.g. `repr({}) = {}`
and `repr(fun(t) -> [#a]) = fun(repr(t)) -> [#a]`. This makes a type annotation usable as
a sort of type constructor for an abstract type, which can be used to either construct
the abstract type (in expression position) or deconstruct it (in pattern position). This
also allows for simply annotating the whole type from the outside, similar to writing a
module signature in ML:

```
abstract t in
  the {.make : fun() -> t, .get : fun(t) -> [#a]}
      {.make() = #a, .get(x) = x}
```

The underlying type of an abstract type may not refer back to the abstract type itself;
recursion goes through `rec` types instead.

### Dependencies

#### Function dependencies

Sometimes a function may work on a generic type of data, but it may depend on certain
functionality associated with the type, like an `equal` or `compare` function. In Haskell and
Rust, typeclasses and traits are used to accomplish this. In OCaml, we may use functors
(like `Set.Make`) or normal arguments (like the first argument to `List.equal`).
In Mu, we use dependencies. Every function takes a dependency argument, which is
always a record. In the body of the function, you can use the form `@<label>`, as in
`@compare(a, b)`, or `@mul(x, y)`, which refers to a field of the innermost enclosing
function's dependencies. The whole dependency record can also be bound by a pattern,
as the last parameter with the keyword `using`, as in `fun(a, b, using deps) -> body`.
The type of the dependency parameter is inferred via normal type inference. In the
application form, the dependency is specified as the last argument, again with
`using`, as in `f(a, b, using c)`. Dependencies are never passed along implicitly: not
including the dependency argument is the same as passing an empty record.

#### Package dependencies

The `@<label>` form can also be used at the top level of a file, for indirect
inter-package dependencies. To directly rely on another package, the expression
`import <hash> using <deps>` is used, where `<hash>` is the BLAKE3 hash of the file,
and `<deps>` is an expression evaluating to a record, to pass as that package's
dependencies. Externally, registries can be used as mappings from a petname to the BLAKE3
hash representing a package. File trees form a local registry with file paths as petnames.


## Editing and evaluation environment

Although the current bootstrapping interpreter parses code in a familiar text format, the
language is designed to be both programmed and run within its own graphical environment.
The canonical format for storing and communicating code is not the text format used by the
bootstrap system, but a simple binary format (yet to be designed) so that content hashing
is unaffected by code formatting concerns.

### Notation

On top of the language, we introduce a "notation" system, present both in the literal forms
of the language as well as the values that it outputs. (NOTE: the notation system is still
very early in its design, and is mostly a set of ideas at this point.) Notation serves a wide
variety of purposes in Mu. Numeric types in Mu are based on Peano numbers, but with the
notation system, they may be written and displayed in the ordinary numeric notation you would
expect. Values like lists of records, or maps from keys to values may be written and displayed
as tables, as you might write them in a spreadsheet.

The domain of the notation system in fact includes much of what you find in HTML, MathML, and
SVG - structured documents, mathematical notation, and vector graphics.
