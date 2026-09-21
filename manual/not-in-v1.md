---
title: Not in v1
slug: not-in-v1
order: 16
summary: What MuroTT v1 refuses, on purpose.
---

# Not in v1

In brief: these are not missing features to patch in a weekend. They are out of the theory. If a user asks for them, say no and point here.

## Refused

- `Type : Type`
- Cubical primitives
- Tactics
- Implicits
- Unification
- Metavariables / holes
- Extra quantities beyond affine, `+`, `-`
- User-defined ν-predicates (only Stream / Always / `~` as specified)
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
- Closed evidence of Empty is proved for Core terms (no application or rewrite) in `agda/Muro/Consistency.agda`.
- The full consistency statement is not proved.
- Example twins are not a proof that a `.muro` file is correct.

## If you need a hole

You do not have one. Write the motive. Write the binder. If conversion fails, write a `rewrite` or a `match` until `refl` checks.

That is the language.
