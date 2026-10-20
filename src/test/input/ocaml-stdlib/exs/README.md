# Writing examples

Each `.exs` file starts with a comment line listing the `.types` files it depends on. Every
other line that isn't blank and doesn't start with `//` is one example.

Each example is checked two ways when it is loaded (`splitOCamlExamples`):

- our type checker, which is plain Hindley-Milner, using the types in `../types`;
- ocamlc, as the ground truth.

If they disagree on any example, loading fails. The rules below keep them agreeing. Each rule
covers a place where OCaml is not Hindley-Milner.

## Syntax

- Application: `(f x y)`. Parentheses group, as in `(f (g x))`.
- Lambda: `(fun x y -> body)`. The body is the rest of the list, read as an application, so
  `(fun x -> f x)` means `(fun x -> (f x))`.
- Let: `(let x = value in body)`. Not recursive: `x` is bound in `body` only.
- A lambda or let must be a list of its own wherever it appears: `(f (fun x -> x))`, never
  `(f fun x -> x)`.
- A bound name is an OCaml variable name: a lowercase letter or `_`, then letters, digits, `_`
  or `'`. No OCaml keywords. `_` binds nothing and can't be used.
- `Num`, `Str`, `Char`, `Flt` and `Nil` stand for `1`, `"s"`, `'a'`, `1.` and `[]`. ocamlc sees them
  replaced as plain text, so no other name may contain those strings: not `xNil`, not `myStr`.

Lambdas and lets are parsed, but not loaded yet: `splitOCamlExamples` drops them until our type
checker handles them. See `binders-next.md` at the repository root.

## Lets: avoid the value restriction

Hindley-Milner generalizes every let, so a let-bound name can be used at several types. OCaml
generalizes a let only when its value is a *syntactic value*:

- a name, like `List.cons`;
- a lambda, like `(fun x -> List.cons x Nil)`;
- a let whose value and body are both syntactic values.

Anything else is not a syntactic value. That includes any application, even a partial one:
`(ref Nil)`, `(List.rev Nil)`, `(List.map (fun x -> x))`.

**Rule: don't use a let-bound name at two different types unless its value is a syntactic
value.**

| Example | OK? |
|---|---|
| `(let id = (fun x -> x) in ((fun a b -> b) (id Num) (id Str)))` | yes: the value is a lambda |
| `(let l = (List.rev Nil) in (List.cons Num l))` | yes: `l` is used at one type |
| `(let f = (List.map (fun x -> x)) in ((fun a b -> b) (f (List.cons Num Nil)) (f (List.cons Str Nil))))` | **no**: OCaml rejects it, Hindley-Milner accepts it |

To fix one that breaks the rule, write the value as a lambda:
`(let f = (fun l -> List.map (fun x -> x) l) in ...)`.

The rule is stricter than OCaml. OCaml also generalizes a non-value when the type variable only
appears in covariant positions, so `(let l = (List.rev Nil) in ((fun a b -> b) (List.cons Num l)
(List.cons Str l)))` is accepted by both. Following the rule means not having to know which
positions count.

The benchmark variant `thunk-lets` (`./gradlew bench --args="... --variant thunk-lets"`) checks
each example with ocamlc as `let x () = value`, with each use of `x` as `x ()`. That makes OCaml
generalize every let the way Hindley-Milner does, so the rule doesn't matter there. The default
checks examples exactly as written.

## Labelled arguments

**Not implemented yet.** The type parser can't read labels on `main`.

Planned handling: our type checker treats a labelled parameter as an ordinary positional one,
in the order the signature declares it. For `val value : 'a option -> default:'a -> 'a`, our
type is `'a option -> 'a -> 'a`. When an example is printed for ocamlc, the label is written at
that argument: `(Option.value o d)` becomes `Option.value o ~default:d`.

That only works where the component is applied to the labelled argument. So:

**Rule: a component with labelled parameters must be the head of an application, and must be
applied at least up to its last labelled parameter.**

| Example | OK? |
|---|---|
| `(Option.value (Option.some Num) Num)` | yes |
| `((fun g -> g Option.none Num) Option.value)` | **no**: passed as a value, so there's nowhere to put `~default` |
| `((fun h -> h Num) (Option.value Option.none))` | **no**: not applied up to `default` |
| `(let v = Option.value in v Option.none Num)` | **no**: applied under another name, so the printer doesn't know to label it |

Wrap it in a lambda if you need it as a value: `(fun o d -> Option.value o d)`.

Until the label is printed, ocamlc sees `Option.value o d` with the label left out. OCaml allows
that only in a full application whose result type is not a type variable:
`ListLabels.iter print_int l` (result `unit`) is fine. `Option.value` returns `'a`, so ocamlc
reads `(Option.value (Option.some Num) Num)` as passing `Num` to the result, not as the
default, and rejects it. `(Option.value Option.none Num)` is accepted, but as a partial
application of type `default:(int -> 'b) -> 'b`, not as an `int`.

## Optional arguments

Optional parameters (`?name:`) are left out of our types entirely:
`val create : ?random:bool -> int -> ('a, 'b) t` is `int -> ('a, 'b) t`. **Not implemented yet**
either.

**Rule: never pass an optional argument, and apply a component with optional parameters
directly to the first positional argument after them.** OCaml then fills in the defaults:
`(Hashtbl.create Num)` is fine.

Passing such a component as a value is not. Whether OCaml drops the optional parameters then
depends on the order it checks things in, which our type checker does not model.
`(List.map (fun f -> f Num) (List.cons Hashtbl.create Nil))` is rejected by ocamlc. Write
`(fun n -> Hashtbl.create n)` instead.
