---
title: Indexed data
slug: indexed
order: 7
summary: Fin, Vec, and lookup without a runtime bounds check.
---

# Indexed data

In brief: constructor targets are compared with conversion. `suc` is inverted, so `vcons` against `Vec A (suc m)` forces the length. Motives bind the indices, then the scrutinee. If the types line up, `lookup` has no runtime bounds check.

## Fin and Vec

From `examples/vec.muro`:

```
data Fin : Nat → Type where
  fzero : Π (n : Nat) → Fin suc(n)
  fsuc  : Π (n : Nat) → Fin n → Fin suc(n)

data Vec (A : Type) : Nat → Type where
  vnil  : Vec A 0
  vcons : Π (n : Nat) → A → Vec A n → Vec A suc(n)
```

`Fin n` is a position smaller than `n`. `Vec A n` is a vector of length `n`. There are no metavariables: you write the length arguments.

## Motives with indices

The motive is a telescope: first the indices, then the scrutinee.

```
match i motive (λ (k : Nat) → λ (_ : Fin k) → Vec A k → A)
  | fzero m => …
  | fsuc m j => …
```

`lookup` returns a function `Vec A k → A`, then applies it to `xs`. That is how the index `k` stays aligned with the vector you eliminate.

```
def lookup : run Π (-A : Type) → Π (-n : Nat) → Π (i : Fin n) → Π (xs : Vec A n) → A :=
  λ (-A : Type) → λ (-n : Nat) → λ (i : Fin n) → λ (xs : Vec A n) →
    (match i motive (λ (k : Nat) → λ (_ : Fin k) → Vec A k → A)
      | fzero m =>
          λ (ys : Vec A suc(m)) →
            (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → A)
              | vnil => 0
              | vcons p a as => a)
      | fsuc m j =>
          λ (ys : Vec A suc(m)) →
            (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → A)
              | vnil => 0
              | vcons p a as => lookup A p j as)) xs
```

`n` is erased: it only appears in types, and the emitted `lookup` does not take it. `lookup` descends on `i`: `j` (from `fsuc m j`, a field of `i`) is passed at that position. `as` is a field of `ys`, a λ-bound variable, and is not smaller: matching a variable that is not an argument, or a computed value, exposes nothing a self-call may descend on. Keeping `n` unerased also checks; the checker finds the argument to descend on.

The `vnil` branches are well-typed empty cases: conversion has already forced `suc(m)` against `0` to be impossible in a consistent book, but the surface still asks you to write a branch. The body `0` is a placeholder the checker accepts in that impossible corner of the motive; a real lookup never takes it when `Fin n` and `Vec A n` agree.

`ones1` is a vector of length one. `lookup-ok` is `refl`:

```
def ones1 : run Vec Nat suc(0) :=
  vcons 0 (suc 0) vnil

def lookup-ok : evidence {lookup Nat suc(0) (fzero 0) ones1 ≡ suc 0 : Nat} :=
  refl
```

## Running it

```
{:ok, src} = Muro.emit_file("examples/vec.muro", Muro.Vecs)
Code.eval_string(src)
Muro.Vecs.lookup({:fzero, 0}, Muro.Vecs.ones1())
# {:suc, 0}
```

`A` was erased, so the Elixir arity starts at `n`. `n` is Peano `{:suc, 0}`. There is no bounds check in the emitted function: the index and the vector were already the same length in the type.

Next: [Streams](streams.md).
