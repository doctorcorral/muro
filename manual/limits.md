---
title: Limits
slug: limits
order: 16
summary: What the language does not do. Facts about the checker, not a roadmap.
---

# Limits

In brief: this is what the parser and checker refuse today. It is a description of the language, not a version number and not a list of things to add later.

## The checker does not accept

- `Type : Type`
- A kind as a small type: `Π (x : A) → Type : Type`, `Type × A : Type`, a constructor field of type `Type`
- Cubical primitives
- Tactics
- Implicits
- Unification
- Metavariables / holes
- Quantities other than affine, `+`, and `-`
- User-defined ν-predicates (Stream, Always, and `~` are the ones that exist)
- `+` on Stream
- `+` on Either, or on `P → Empty`
- Typing raw Elixir
- Emitting spec or evidence
- Identity on `F32` or `Tensor F32 S`
- Treating `I64` as `Nat`
- A second index language for tensor shapes
- Redeclaring Nat, Unit, Empty, or Stream as `data`
- A fourth term representation
- Raw HOAS (`Tm → Tm`) as inductive syntax
- Tags other than `run`, `run internal`, `spec`, `evidence`

## Former names (history, not syntax)

The language was once described as *nothing dead runs* and *a proof never becomes a run*. Those words are not tags. The tags are `spec`, `evidence`, and `run`.

## What is proved, and what is not

- The mode wall is proved for the core fragment in `agda/Muro/Wall.agda`.
- In `agda/Muro/Consistency.agda`: no closed normal evidence term has type Empty, and closed evidence terms make progress. Conversion there is a relation (`agda/Muro/Convert.agda`), and the modules are checked under `--safe`.
- The full consistency statement (`Empty-evid`) is not proved. Preservation and normalisation of closed evidence are its open hypotheses (`Empty-evid-from`).
- `Type` is impredicative and kinds are not small types. Before the kind/small-type distinction was enforced, the checker accepted `Π (x : A) → Type : Type`, which retracts `Type` into a small type; that was a bug in the calculus, not in a program, and it is fixed in both Agda and Elixir.
- Example twins are not a proof that a `.muro` file is correct.

## If you need a hole

You do not have one. Write the motive. Write the binder. If conversion fails, write a `rewrite` or a `match` until `refl` checks.

That is the language.
