---
title: Extending the kernel
slug: extending
order: 15
summary: How to change the type theory. Agda first, then Elixir.
---

# Extending the kernel

In brief: this is Job B. If you only want a program, stop and go back to [Start](start.md). Order is mandatory. If Agda and Elixir disagree, Agda wins.

## Order

1. **Agda syntax** (`agda/Muro/Syntax.agda`) if you add a constructor — both `Tm n` and `PTm V`.
2. **Subst** (`agda/Muro/Subst.agda`): `wk`, `sub`, `toPHOAS`, `unembed`. Pattern-lambdas passed to `sub` do not compute; use a named function (`instσ`, `motSucσ`).
3. **Check** (`agda/Muro/Check.agda`): a `decide` clause. Mixfix in `Muro.Judgement` is `σ , Γ ⊢[ m ] e ⇒ A ⊣ u`.
4. `make agda` until the example twin decides (`half_ok-checks` is `refl` for the canonical book). Twins are examples of the rules, not a proof that the book is correct.
5. **Elixir mirror**, same shapes, each checker clause commented with the Agda constructor (`⇒-var-run`, `⇐-refl`, …):
   - `lib/muro/ast.ex`
   - `lib/muro/subst.ex`
   - `lib/muro/check.ex`
   - `lib/muro/parser.ex` / `lib/muro/emit.ex` if it is surface or run code
6. `mix test` and `mix muro.check`.

Do not add a fourth representation. Do not use raw HOAS (`Tm → Tm`) as inductive syntax.

`toPHOAS` / `unembed` live in `agda/Muro/Subst.agda`. Elixir `Muro.Ast.to_db/2` sends named FOAS to de Bruijn (unbound names become `{:def, name}`).

## Elixir constraints

- ASCII identifiers only. No unicode primes, no mixed-script atoms.
- Do not define local `hd/1`.
- Guards cannot call ordinary `defp` helpers.

## What Agda is

Agda holds the rules. It is not a certificate that a `.muro` file is correct. It is not what `mix muro.check` runs.

- `Muro.Check` — fuelled decision procedure.
- `Muro.Judgement` — inductive ⊢ for the core fragment.
- `Muro.Wall` — mode wall lemmas. No promotion.
- `Muro.Consistency` — closed evidence of Empty, for Core terms (no application or rewrite). The full statement is not proved. `Empty-evid` is not proved.

Example twins (`Example*.agda`) are examples of those rules.

## Build

Agda 2.8+ and standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` is `agda --no-libraries -i agda -i vendor/agda-stdlib/src`. The stdlib checkout ships extra `.agda-lib` files that must not be loaded.

CI runs the Elixir job and `make agda` on every push and pull request.

## Named FOAS (parser output)

```
{:var, name}
:typ | :nat | :ze | {:su, t} | :unit | :one | :empty
{:pi, qty, a, name, b}
{:lam, qty, a, name, t}
{:app, f, a}
{:mnat, e, x, p, z, y, s}
{:memp, e, x, p}
{:munit, e, x, p, u}          -- kernel only
{:idt, ty, a, b}
:rfl
{:rwt, eq, x, p, t}
{:def, name}
{:ann, e, a}                  -- kernel only
{:prod, a, b} | {:pair, a, b} | {:fst, t} | {:snd, t}
{:stream, a} | {:unf, seed, f} | {:ucons, s}
{:sum, a, b} | {:left, t} | {:right, t}
{:msum, e, x, p, a, l, b, r}
```

`qty` is `:affine | :reuse | :erased`. A book entry:

```
%{name: "half", mode: :run, export: true, type: named, body: named}
%{name: "IsEven", mode: :spec, type: named, body: named}
%{name: "half_ok", mode: :evidence, type: named, body: named}
```

`export` is present only on `:run` (`true` → `def`, `false` → `defp`).

De Bruijn drops the name strings: `{:pi, q, a, b}`, `{:lam, q, a, t}`, `{:mnat, e, p, z, s}` with index 0 = nearest binder.

## Bidirectional rules (v1)

```
σ , Γ ⊢[ m ] e ⇒ A     infer
σ , Γ ⊢[ m ] e ⇐ A     check
```

Hard rules you must not relax without a new theory:

1. A run or evidence variable is used at most once, unless `+` on Data.
2. Run and evidence recursion must descend on a non-erased argument. Spec does not check descent.
3. No promotion. Erased variables have no computational use.
4. Emitted code is run only.

Conversion: syntactic equality first; then stuck-def congruence when the first argument is not constructor-headed; then WHNF. Fuel is for conversion only.

After you change the kernel, update this manual so `manual/` stays the language book. Do not put the change only in `@moduledoc`.
