---
title: Terms
slug: language
order: 4
summary: Type, Π, λ, match, quantities, and the book.
---

# Terms

In brief: one sort `Type`. Binders are written. Application is juxtaposition. `match` takes an explicit motive. Affine is the default.

## The book

A `.muro` file is a **book**: a sequence of `ν`, `data`, and `def` entries.

```
def name : tag type := body
```

The tag is `run`, `run internal`, `spec`, or `evidence`. There is no other tag. These words are rejected as tags (they remain ordinary identifiers): `live`, `dead`, `proof`, `proof evidence`, `ghost`, `comp`, `export`.

Forward references are allowed. The checker sees every definition when it checks any one of them.

## Type

There is one sort, `Type`. It is not `Type : Type`. `Type` itself is erased: you do not compute with it.

A *small type* is a term of type `Type`: `Nat`, `Π (n : Nat) → Nat`, `Π (X : Type) → X`, `IsEven 2`. A *kind* is `Type` or `Π (x : A) → K` with `K` a kind: `Π (n : Nat) → Type` is the kind of `IsEven`. Kinds are well-formed, so they can be the type of a `def` and the type of a binder, but a kind is not a term of type `Type`. The checker refuses `Π (_ : Unit) → Type`, `Type × Unit`, and a constructor field of type `Type` where a small type is expected. Without that refusal `Type` would be a retract of a small type and the sort would be inconsistent (Girard's paradox).

`Type` is impredicative: `Π (X : Type) → X` is itself in `Type`. That is the design, not an accident, and it is why a consistency proof for the calculus cannot come from a set-theoretic model in Agda.

Primitive types you can write as atoms:

| Atom | Meaning |
| --- | --- |
| `Type` | The sort |
| `Nat` | Peano naturals |
| `Unit` | One constructor, `tt` |
| `Empty` | No constructors |
| `I64` / `F32` | Machine scalars; see [Machine numbers](machine.md) |
| `Stream A` | Greatest fixed point; see [Streams](streams.md) |

`Nat`, `Unit`, and `Empty` as *types* are spec formers. You infer them only in spec. Their *constructors* (`0`, `suc`, `tt`) compute in run.

## Binders and quantities

A binder is always parenthesized.

```
(n : Nat)        affine (default): at most one run/evidence use
(+ n : Nat)      reuse: only if the type WHNFs to Data
(- e : IsEven n) erased: compile-time; cannot be used computationally
```

The `+` or `-` sits immediately before the name, inside the parentheses. `(-A : Type)` and `(- A : Type)` both parse.

**Data** (after WHNF) for `+`: `Nat`, `Unit`, `Empty`, `I64`, `F32`, `Tensor`, or a user `data` type whose *parameters* are Data. Indices do not have to be Data. `List A` is Data iff `A` is. `List (Nat → Nat)` is not, so you cannot write `+xs : List (Nat → Nat)`.

`Stream` and `Either` are not Data. There is no `+` on a stream or on a refutation `P → Empty`.

In spec, uses are forgotten. You can mention an affine variable twice while building a type.

In run and evidence, using an affine variable twice is an error: `affine variable used twice`. Using an erased variable computationally is an error: `erased variable used computationally`.

## Π and λ

```
Π (n : Nat) → Nat
λ (n : Nat) → suc(n)
```

ASCII: `Pi`, `lam`, `->`.

A non-dependent arrow `A → B` is `Π (_ : A) → B` with an affine ignored binder.

Application is juxtaposition: `f a b`. `motive`, `in`, and `def` never start an argument.

## match

Every eliminator writes its motive. The motive is the family you return in, with the scrutinee bound.

Nat:

```
match n motive (λ x → P)
  | 0 => tz
  | suc p => ts
```

`x` is bound in `P`. `p` is bound in `ts`. `suc p` here is a pattern binder, not `suc` applied to a term.

Empty:

```
matchEmpty e motive (λ _ → P)
```

There are no constructors. If you have an inhabitant of `Empty`, you may return any `P`.

Data (one named branch per constructor):

```
match m motive (λ _ → A)
  | nothing => d
  | just a  => a
```

Motives are written in parentheses. Nested λ in the motive cover index binders (see [Indexed data](indexed.md)).

## Products

`A × B` (ASCII `*`) is a pair type. `(a, b)` is a pair. A pair is opened with `let`:

```
let (a, b) = e in t
```

`e` must have a pair type `A × B`; `t` is checked against the expected type with `a : A` and `b : B` in scope, each affine. `let (a, b) = (u, v) in t` reduces to `t` with `a := u`, `b := v`. Like `λ`, a `let` has no type of its own: it is checked against an expected type, so it may not be the head of an application.

`let` is the way to consume an affine pair: a pair-typed variable `p` may be used once, and `plus (fst p) (snd p)` uses it twice. `let (x, y) = p in plus x y` uses it once and both components once. `fst` and `snd` still project; `head s` is `fst (uncons s)` and `tail s` is `snd (uncons s)`. The projections are accepted by the checker but are outside the fragment the Agda proofs cover; `let` is inside it (see [Limits](limits.md)).

## Recursion and descent

A definition in `run` or `evidence` descends on one of its non-erased arguments, the same one at every self-call. At that position a self-call must pass a smaller variable: one that came from a `match` on that argument, or on a variable already smaller (the `suc` predecessor, a constructor argument whose type is `D …`, the tail of a list, …). The other positions may hold anything. The checker finds the position: it tries the first non-erased argument, then each later one, and a definition with no self-call passes at once.

Three things are not descent. A smaller variable passed at another position (`f (suc (suc y)) xp` when `xp` came from `x`, the first argument). The fields of a `match` on a computed value or on a λ-bound variable that is not the argument (`match (f x) …`, `match ys …` under `λ ys →`): the match is fine, its fields are not smaller. The definition itself unapplied (`apply f n`): in run and evidence a self-reference must be the head of a call.

Spec does not check descent. `IsEven` may recurse on `p` after two `suc` matches because it is a spec.

A typical run recursion looks like `plus`:

```
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

`np` is smaller than `n`. `plus np m` is allowed. `plus n m` inside the `suc` branch is not.

## The half example, as a reader

`examples/half_ok.muro` puts the three modes in one file.

- `plus` — run. Adds Peano numbers.
- `IsEven` — spec. A family `Nat → Type`. `0` is even (`Unit`). `1` is odd (`Empty`). `suc(suc p)` is even iff `p` is.
- `half` — run. Drops two `suc` at a time.
- `plus_suc` — evidence. `{plus n suc(m) ≡ suc(plus n m) : Nat}`.
- `half_ok` — evidence. If `n` is even, `{plus (half n) (half n) ≡ n : Nat}`.

`half` of eight is four. The proof is `match`, `refl`, `rewrite`, and `matchEmpty`. It is not emitted.

Next: [Identity](identity.md).
