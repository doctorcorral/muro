# Muro

**nothing dead runs.**

An explicit affine dependent type theory: Elixir checks it, Agda specifies it, only live terms run.

Named after the live/dead wall. Dead terms (types, erased arguments, equations, paradoxes) never become live evidence or running code.

## Layout

| Layer | Form |
| --- | --- |
| Elixir parser / pretty / emit | named FOAS (quoted tuples or `.muro`) |
| Executable check / subst | PHOAS in Agda; de Bruijn in both Agda and Elixir |
| Metatheory (soundness, no-promotion) | de Bruijn `Tm n` in Agda |

`toPHOAS` and `unembed` (PHOAS → de Bruijn) live in `agda/Muro/Subst.agda`. Raw HOAS (`Tm → Tm`) is not the inductive syntax.

```
agda/Muro/          specification (source of truth for ⊢)
lib/muro/           Elixir checker, parser, emit
examples/half_ok.muro
```

## Theory (MuroTT v1)

Bidirectional, two modes:

- Γ ⊢ᵐ e ⇒ A  infer
- Γ ⊢ᵐ e ⇐ A  check

m ∈ {live, dead}.

Syntax: one `Type` (not Type : Type), Π / λ / app, quantities (live affine by default, `+` reuse only if the type is Data, `-` erased), inductive families enough for Nat, Empty, Unit, and `IsEven n`, identity with `refl` when both sides compute equal, rewrite with explicit motive, match with explicit motive.

Hard rules:

- A live variable is used at most once (unless `+` on Data).
- Live recursion must descend on a live argument.
- No promotion: there is no rule taking a dead derivation to a live one.
- `main` / emitted code is live only.

Agda `Muro.Check` is the spec. If Agda and Elixir disagree, Agda wins.

## The example

```
IsEven : Nat → Type
half   : Nat → Nat
half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
```

Proofs are ordinary terms: match + refl + rewrite with motive.

## Build

Agda 2.8+ and the standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

Elixir 1.15+:

```
mix test
```

`Muro.Check.check_sig/1` returns `:ok` on the book. Live defs emit to ordinary Elixir; `half` of eight is four.

## Names

| | |
| --- | --- |
| Language | Muro |
| Theory | MuroTT |
| Files | `.muro` |
| Elixir | `Muro`, `Muro.Check`, `Muro.Emit` |
| Agda | `Muro.*` |
