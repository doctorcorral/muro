# Muro

**A proof never becomes a run.**

An explicit affine dependent type theory: Elixir checks it, Agda specifies it, only run terms run.

Named after the wall between run and proof. Types, erased arguments, equations, and paradoxes never become running code. (Formerly phrased *nothing dead runs*; that is metaphor, not syntax.)

## Layout

| Layer | Form |
| --- | --- |
| Elixir parser / pretty / emit | named FOAS (quoted tuples or `.muro`) |
| Executable check / subst | PHOAS in Agda; de Bruijn in both Agda and Elixir |
| Metatheory (soundness, no-promotion) | de Bruijn `Tm n` in Agda |

`toPHOAS` and `unembed` (PHOAS → de Bruijn) sit in `agda/Muro/Subst.agda`. Raw HOAS (`Tm → Tm`) is not the inductive syntax.

```
agda/Muro/          specification (source of truth for ⊢)
lib/muro/           Elixir checker, parser, emit
examples/half_ok.muro
examples/internal_ok.muro
```

## Theory (MuroTT v1)

Bidirectional, two judgment modes, three surface tags:

- Γ ⊢ᵐ e ⇒ A  infer
- Γ ⊢ᵐ e ⇐ A  check

| Tag | Judgment | Emit |
| --- | --- | --- |
| `run` | computational (`:run`) | `def` |
| `run internal` | same judgment | `defp` |
| `proof` | erased types/proofs (`:proof`) | omit |

m ∈ {run, proof}. Emit visibility is an Elixir-only flag on `run`.

Syntax: one `Type` (not Type : Type), Π / λ / app, quantities (affine by default, `+` reuse only if the type is Data, `-` erased), inductive families enough for Nat, Empty, Unit, and `IsEven n`, identity with `refl` when both sides compute equal, rewrite with explicit motive, match with explicit motive.

Hard rules:

- A run variable is used at most once (unless `+` on Data).
- Run recursion must descend on a run argument.
- No promotion: there is no rule taking a proof derivation to a run one.
- Emitted code is run only.

Agda `Muro.Check` is the spec. If Agda and Elixir disagree, Agda wins.

## The example

```
IsEven : Nat → Type
half   : Nat → Nat
half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
```

Proofs are ordinary terms: match + refl + rewrite with motive.

```
def plus    : run   Π (n : Nat) → Π (m : Nat) → Nat := ...
def half    : run   Π (n : Nat) → Nat := ...
def IsEven  : proof Π (n : Nat) → Type := ...
def half_ok : proof Π (n : Nat) → Π (e : IsEven n) → {plus (half n) (half n) ≡ n : Nat} := ...
```

## Build

Agda 2.8+ and the standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

Elixir 1.15+:

```
mix test
mix muro.check
```

`Muro.Check.check_sig/1` returns `:ok` on the book. Run defs emit to ordinary Elixir; `half` of eight is four.

## Names

| | |
| --- | --- |
| Language | Muro |
| Theory | MuroTT |
| Files | `.muro` |
| Elixir | `Muro`, `Muro.Check`, `Muro.Emit` |
| Agda | `Muro.*` |
