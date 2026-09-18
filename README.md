# Muro

**A spec never becomes evidence. Evidence never becomes a run.**

An explicit affine dependent type theory: Elixir checks it, Agda specifies it, only run terms run.

Named after the wall between spec, evidence, and run. Types, erased arguments, equations, and paradoxes never become running code. (Formerly *nothing dead runs* / *a proof never becomes a run*; those are history, not syntax.)

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

Bidirectional judgments:

- Γ ⊢ᵐ e ⇒ A  infer
- Γ ⊢ᵐ e ⇐ A  check

m ∈ {run, spec, evid}.

| Tag | What | Affinity + descent | Emit |
| --- | --- | --- | --- |
| `run` | program | yes | `def` |
| `run internal` | same | yes | `defp` |
| `spec` | type / family / signature | no | omit |
| `evidence` | theorem | yes (same tax as run) | omit |

Emit visibility is an Elixir-only flag on `run`.

Syntax: one `Type` (not Type : Type), Π / λ / app, quantities (affine by default, `+` reuse only if the type is Data, `-` erased), inductive families enough for Nat, Empty, Unit, and `IsEven n`, identity with `refl` when both sides compute equal, rewrite with explicit motive, match with explicit motive.

Hard rules:

- A run or evidence variable is used at most once (unless `+` on Data).
- Run and evidence recursion must descend on a non-erased argument.
- No promotion: spec ↛ evidence, evidence ↛ run, spec ↛ run.
- Emitted code is run only.

Agda `Muro.Check` is the spec. If Agda and Elixir disagree, Agda wins.

## The example

```
IsEven : Nat → Type
half   : Nat → Nat
half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
```

Evidence is an ordinary term: match + refl + rewrite with motive.

```
def plus     : run      Π (n : Nat) → Π (m : Nat) → Nat := ...
def IsEven   : spec     Π (n : Nat) → Type := ...
def half     : run      Π (n : Nat) → Nat := ...
def plus_suc : evidence Π (n : Nat) → Π (m : Nat) →
                          {plus n suc(m) ≡ suc(plus n m) : Nat} := ...
def half_ok  : evidence Π (n : Nat) → Π (e : IsEven n) →
                          {plus (half n) (half n) ≡ n : Nat} := ...
```

## Build

Agda 2.8+ and the standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

Elixir and OTP via [mise](https://mise.jdx.dev/) (`mise.toml` pins `latest` stable):

```
mise install
mix test
mix muro.check
```

`Muro.Check.check_sig/1` returns `:ok` on the book. Run defs emit to ordinary Elixir; `half` of eight is four.

CI (GitHub Actions) runs Elixir tests and `make agda` on every push and pull request.

## Names

| | |
| --- | --- |
| Language | Muro |
| Theory | MuroTT |
| Files | `.muro` |
| Elixir | `Muro`, `Muro.Check`, `Muro.Emit` |
| Agda | `Muro.*` |
