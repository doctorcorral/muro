# Muro

**A spec never becomes evidence. Evidence never becomes a run.**

An explicit affine dependent type theory. Elixir parses, checks, and emits it. Agda specifies the judgments. Only run terms become running code.

Named after the wall between spec, evidence, and run. Types, erased arguments, equations, and paradoxes never execute. (Formerly *nothing dead runs* / *a proof never becomes a run*; those are history, not syntax.)

If Agda and Elixir disagree, Agda wins.

---

## One-shot (humans and agents)

Two jobs. Do not mix them.

| You want to… | Do this |
| --- | --- |
| Add a Muro program | Write a `.muro` file against the grammar below. Check with `mix muro.check path.muro`. Do not change Agda or the Elixir kernel. |
| Change the type theory | Edit Agda `Muro.Check` first until it decides the new example. Then add the matching Elixir clause, tagged with the ⊢ constructor. |

Copy-paste skeleton:

```
-- comments start with --
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

Then:

```
mix muro.check examples/your_file.muro
```

A definition is in the book the moment `Parser.parse/1` returns it. The checker sees the whole book (forward references are allowed). Emit keeps only `run`.

---

## Surface grammar

This is the grammar `lib/muro/parser.ex` actually implements. ASCII aliases are in parentheses.

```
book       ::= (nu | data | def)*
nu         ::= ("ν" | "nu") "Stream" binder ":" term "where" "uncons" ":" term
data       ::= "data" ident binder* ":" telescope "where" (ident ":" term)+
telescope  ::= "Type" | binder ("→" | "->") telescope | term ("→" | "->") "Type"
def        ::= "def" ident ":" tag term ":=" term
tag        ::= "run" "internal"? | "spec" | "evidence"

term       ::= atom atom*                  -- juxtaposition is application
             | term ("×" | "*") term
             | term "⊎" term               -- desugars to Either
             | term "::" term              -- desugars to cons
             | term ("→" | "->") term      -- non-dependent, = Π (_ : A) → B
atom       ::= "Type" | "Nat" | "I64" | "F32" | "Unit" | "Empty" | "refl" | "tt" | "0"
             | suc | pi | lam | match | matchEmpty | rewrite | idt
             | stream | unfold | uncons | "fst" atom | "snd" atom
             | "head" atom | "tail" atom
             | "Tensor" atom atom | "addi" atom atom | "muli" atom atom
             | "addt" atom atom | "toI64" atom | "packI" atom atom
             | "[]"                        -- desugars to nil
             | "(" term ")" | "(" term "," term ")"
             | ident

suc        ::= "suc" "(" term ")" | "suc" atom
stream     ::= "Stream" atom
unfold     ::= "unfold" atom atom         -- seed, λ s → (head, next_seed)
uncons     ::= "uncons" atom
qty        ::= "+" | "-" | ε               -- ε = affine (default)
binder     ::= "(" qty ident ":" term ")"
pi         ::= ("Π" | "Pi") binder ("→" | "->") term
lam        ::= ("λ" | "lam") binder ("→" | "->") term

match      ::= "match" term "motive" mot
               "|" "0" "=>" term
               "|" "suc" ident "=>" term
             | "match" term "motive" mot
               ("|" ident ident* "=>" term)+
matchEmpty ::= "matchEmpty" term "motive" mot
rewrite    ::= "rewrite" term "motive" mot "in" term
mot        ::= "(" ("λ" | "lam")? (ident | binder) ("→" | "->") term ")"
               -- nested λ in the body cover index binders (Vec / Fin)
idt        ::= "{" term ("≡" | "==") term ":" term "}"

ident      ::= [A-Za-z_][A-Za-z0-9_-]*
comment    ::= "--" through end of line
space      ::= [ \t\n\r] | comment
```

Application is juxtaposition (`f a b`). `motive`, `in`, and `def` never start an argument. Digits start atoms, so `| 0 =>` parses.

Rejected as tags (not as ordinary identifiers): `live`, `dead`, `proof`, `proof evidence`, `ghost`, `comp`, `export`. There is no other tag.

Not in the surface (present in the kernel AST only): `matchUnit`, annotations `{e : A}`, raw de Bruijn.

### Binder quantities

```
Π (n : Nat) → …        affine (default): at most one run/evidence use
Π (+ n : Nat) → …      reuse: only if the type WHNFs to Data (Nat, Unit, Empty, I64, F32, Tensor, or a data type whose parameters are Data)
Π (- e : IsEven n) → … erased: compile-time; cannot be used computationally
```

The `+` / `-` sits immediately before the name, inside the parentheses.

### Identity, match, rewrite

```
{plus (half n) (half n) ≡ n : Nat}     identity type  (sides and sort)

match n motive (λ x → P)
  | 0 => tz
  | suc p => ts                        Nat eliminator; motive is explicit

match m motive (λ _ → A)
  | nothing => d
  | just a  => a                       data eliminator; one named branch per constructor

matchEmpty e motive (λ _ → P)          Empty eliminator

rewrite eq motive (λ z → P) in t       eq : {lhs ≡ rhs : A};
                                       t is checked as P[rhs]
```

`refl` checks against `{x ≡ y : A}` only when `x` and `y` convert.

---

## Modes and the wall

m ∈ {run, spec, evid}. Surface word `evidence` is Agda constructor `evid` and Elixir atom `:evidence`.

| Tag | Meaning | Affinity + descent | Emit |
| --- | --- | --- | --- |
| `run` | program | yes | `def` |
| `run internal` | same judgment | yes | `defp` |
| `spec` | type / family / signature | no (uses forgotten) | omit |
| `evidence` | theorem | yes (same tax as run) | omit |

Emit visibility (`def` vs `defp`) is Elixir-only on `run`. Agda `Def` stores `dmode` only.

Promotion is forbidden:

```
spec ↛ evidence
evidence ↛ run
spec ↛ run
```

Using a definition of mode `from` while checking in mode `to`:

| from \ to | run | evidence | spec |
| --- | --- | --- | --- |
| run | yes | yes | yes |
| evidence | no | yes | yes |
| spec | no | no | yes |

Erased Π-arguments and identity sides are checked in spec. Arguments of an **evidence definition** at a call site are also checked in spec (uses discarded), so instantiating a theorem does not consume affine resources. Local affine binders in an evidence λ still fail if used twice.

---

## Kernel (MuroTT v1)

Bidirectional, explicit, no metavariables, no implicits, no unification, no tactics.

```
σ , Γ ⊢[ m ] e ⇒ A     infer
σ , Γ ⊢[ m ] e ⇐ A     check
```

- One sort `Type`. Not Type : Type. `Type` itself is erased.
- Π / λ / app, quantities affine / reuse / erased.
- Inductive families enough for `Nat`, `Empty`, `Unit`, and `IsEven n`.
- Identity `{e₁ ≡ e₂ : A}` with `refl` when both sides compute equal.
- `rewrite` and `match` take an explicit motive. No inference of the motive.

Hard rules:

1. A run or evidence variable is used at most once, unless `+` on Data.
2. Run and evidence recursion must descend on a non-erased argument (a structurally smaller variable from a `match`). Spec does not check descent.
3. No promotion (table above). Erased variables have no computational use.
4. Emitted code is run only. Fallback for a non-run fragment is `raise "erased term"`.

Data (for `+`) after WHNF: `Nat`, `Unit`, `Empty`.

Conversion: syntactic equality first; then stuck-def congruence when the first argument is not constructor-headed; then WHNF. Fuel is for conversion only (Elixir `@fuel 2000`). Infer/check recurse on the term.

---

## Representations

Three, on purpose. Do not add a fourth, and do not use raw HOAS (`Tm → Tm`) as inductive syntax.

| Layer | Form | Where |
| --- | --- | --- |
| Parser / pretty / emit | named FOAS | `lib/muro/{parser,ast,emit}.ex` |
| Check / subst | de Bruijn | `lib/muro/{check,subst}.ex`, `agda/Muro/{Check,Subst}.agda` |
| Examples in Agda | PHOAS `PTm V` | `agda/Muro/Syntax.agda`, `agda/Muro/Example.agda` |
| Metatheory | de Bruijn `Tm n` | `agda/Muro/Syntax.agda` |

`toPHOAS` / `unembed` live in `agda/Muro/Subst.agda`. Elixir `Muro.Ast.to_db/2` sends named FOAS to de Bruijn (unbound names become `{:def, name}`).

### Named FOAS (what the parser emits)

```
{:var, name}
:typ | :nat | :ze | {:su, t} | :unit | :one | :empty
{:pi, qty, a, name, b}
{:lam, qty, a, name, t}
{:app, f, a}
{:mnat, e, x, p, z, y, s}     -- x binds in motive p; y binds in suc branch s
{:memp, e, x, p}
{:munit, e, x, p, u}          -- kernel only; no parser production
{:idt, ty, a, b}              -- {a ≡ b : ty}
:rfl
{:rwt, eq, x, p, t}
{:def, name}
{:ann, e, a}                  -- kernel only; no parser production
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

---

## Adding a `.muro` program

1. Put the file in `examples/`. Use only `run` / `run internal` / `spec` / `evidence`.
2. Every binder is a typed `(x : A)` (or `(+ x : A)` / `(- x : A)`). No implicit arguments.
3. Every `match` / `rewrite` writes `motive (λ x → …)` in parentheses.
4. `suc` on a term is `suc(t)`. `suc p` in a pattern is a binder, not an application.
5. Recursion on `run`/`evidence` must go through `match` and call `f p` where `p` is the `suc` variable (or smaller).
6. Check:

```
mix muro.check examples/your_file.muro
```

7. Emit (run only), from `iex -S mix`:

```
{:ok, src} = Muro.emit_file("examples/your_file.muro", Foo)
IO.puts(src)
```

8. If you want it in the test suite, parse/check/emit in `test/muro_check_test.exs`. The canonical book is also `Muro.Example.book/0` (must stay in sync with `examples/half_ok.muro` and `agda/Muro/Example.agda`).

Emit of Nat: `0` stays `0`; `suc(n)` becomes `{:suc, n}`. Unit constructor `tt` becomes `:tt`. User data is one dialect: a 0-argument constructor is an atom (`:nil`, `:nothing`); otherwise `{:ctor, args…}` (`{:cons, a, as}`, `{:just, a}`). Erased Π-arguments are dropped from the generated arity.

---

## Extending the kernel

Order is mandatory:

1. **Agda syntax** (`agda/Muro/Syntax.agda`) if you add a constructor — both `Tm n` and `PTm V`.
2. **Subst** (`agda/Muro/Subst.agda`): `wk`, `sub`, `toPHOAS`, `unembed`. Pattern-lambdas passed to `sub` do not compute; use a named function (`instσ`, `motSucσ`).
3. **Check** (`agda/Muro/Check.agda`): a ⊢ constructor and a `decide` clause. Mixfix is `σ , Γ ⊢[ m ] e ⇒ A`.
4. `make agda` until the example decides (`half_ok-checks` is `refl` for the canonical book).
5. **Elixir mirror**, same shapes, each checker clause commented with the Agda constructor (`⇒-var-run`, `⇐-refl`, …):
   - `lib/muro/ast.ex`
   - `lib/muro/subst.ex`
   - `lib/muro/check.ex`
   - `lib/muro/parser.ex` / `lib/muro/emit.ex` if it is surface or run code
6. `mix test` and `mix muro.check`.

Elixir constraints: ASCII identifiers only (no unicode primes, no mixed-script atoms). Do not define local `hd/1`. Guards cannot call ordinary `defp` helpers.

---

## The example

`examples/half_ok.muro` is the done bar for the v1 kernel:

```
IsEven : Nat → Type
half   : Nat → Nat
half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
```

```
def plus     : run      Π (n : Nat) → Π (m : Nat) → Nat := …
def IsEven   : spec     Π (n : Nat) → Type := …
def half     : run      Π (n : Nat) → Nat := …
def plus_suc : evidence Π (n : Nat) → Π (m : Nat) →
                          {plus n suc(m) ≡ suc(plus n m) : Nat} := …
def half_ok  : evidence Π (n : Nat) → Π (e : IsEven n) →
                          {plus (half n) (half n) ≡ n : Nat} := …
```

Evidence is an ordinary term: `match` + `refl` + `rewrite` with motives. `half` of eight is four. `examples/internal_ok.muro` is a `run internal` helper (`step` → `defp`) called from a `run` def (`inc` → `def`).

### ν

μ descends (`match` on Nat). ν is a greatest fixed point `ν X. F(X)` with F strictly positive. Stream is the instance `ν X. A × X`. Always is a coinductive family: `Always P s = ν Y. P (head s) × Y` (head satisfies P; the tail is guarded). `σ ~ τ` (ASCII `bisim`) is a coinductive family on two streams: heads equal, tails related (J.J.M.M. Rutten, Elements of Stream Calculus, ENTCS 45 (2001), Theorem 2.1). Only a run Stream becomes an Elixir `Stream`. Always, `~`, and their inhabitants are evidence and are omitted. `+` is still only for Data (`Nat`, `Unit`, `Empty`). A non-productive run or evidence unfold is rejected.

See `examples/zeros.muro`, `examples/nats.muro`, `examples/always.muro`, and `examples/bisim.muro`. IEx:

```
{:ok, src} = Muro.emit_file("examples/nats.muro", Muro.Nats)
Code.eval_string(src)
Muro.Nats.natsFrom(0) |> Stream.take(3) |> Enum.to_list()
# [0, {:suc, 0}, {:suc, {:suc, 0}}]
```

### Data (indexed)

A `data` declaration is a book entry the checker uses. Binders before `:` are parameters; the telescope after `:` before `Type` is indices. Nat, Unit, Empty, and ν stay primitive. There is no Tm constructor named after a user type (Vec, Fin, Maybe, List all use `dty` / `ctor` / `mData`). This pass is indexed data. See `examples/vec.muro`.

```
data Maybe (A : Type) : Type where
  nothing : Maybe A
  just    : A → Maybe A
```

The type former is spec. Constructors compute in run and may appear in evidence. Match has one named branch per constructor and an explicit motive over the scrutinee and its indices. Constructor targets are compared with conversion (no metavariables); `suc` is inverted so `vcons` against `Vec A (suc m)` forces the length argument. A self-call in run or evidence must use a constructor argument whose type is `D …`. Strict positivity: `D` must not occur left of Π in a constructor telescope (`mk : Π (n : Nat) → (Bad n → Nat) → Bad n` is rejected). `Vec A n` is Data iff `A` is Data (the index `n` is Nat).

```
{:ok, src} = Muro.emit_file("examples/vec.muro", Muro.Vecs)
Code.eval_string(src)
Muro.Vecs.lookup({:suc, 0}, {:fzero, 0}, Muro.Vecs.ones1())
# {:suc, 0}
```

`lookup` takes `Fin n` and `Vec A n`; there is no runtime bounds check if the types line up. Maybe and List are the same schema with an empty index telescope; see `examples/maybe.muro`.

### ⊎ / Dec

`A ⊎ B` (ASCII `Either A B`) is `data Either`. `left` / `right` are checked against an expected Either. Match has an explicit motive, same shape as other data.

```
Dec P  =  P ⊎ (P → Empty)
```

`Dec` is a spec: a decision for a particular `P`, not LEM. There is no inhabitant of `Π (P : Type) → Dec P`. Closures `P → Empty` are not Data; no `+` on the refutation. `evenDec` is evidence and is not emitted.

See `examples/even_dec.muro`.

### List

`List A` is `data List` with `nil` / `cons` (ASCII `[]` / `::`). Match has an explicit motive; recursion must descend on the tail. `List A` is Data iff `A` is Data, so `+xs : List Nat` may be reused and `List (Nat → Nat)` may not. See `examples/list.muro`.

```
{:ok, src} = Muro.emit_file("examples/list.muro", Muro.Lists)
Code.eval_string(src)
Muro.Lists.length(Muro.Lists.ones2())
# {:suc, {:suc, 0}}
```

`ones2()` is `{:cons, {:suc, 0}, {:cons, {:suc, 0}, :nil}}`.

### I64 / F32 / Tensor (Nx)

`I64`, `F32`, and `Tensor D S` are spec formers wrapping `%Nx.Tensor{}`. Computed values are run. Nat stays Peano (`0` / `{:suc, n}`). Machine integers are a different type; the only map is `toI64 : Nat → I64` (total on Peano; the example uses small values). Shape is one I64 dimension — not a Peano Nat and not a second index language.

`Tensor D S` is Data, so `+` is allowed. Kernel identity `{e₁ ≡ e₂ : F32}` and `{e₁ ≡ e₂ : Tensor F32 S}` is refused. Emit is ordinary `def` plus `Nx.add` / `Nx.stack` / `Nx.tensor`, not `defn`. Mix depends on `{:nx, "~> 0.9"}` only.

See `examples/nx_add.muro`. IEx:

```
{:ok, src} = Muro.emit_file("examples/nx_add.muro", Muro.NxAdd)
Code.eval_string(src)
Muro.NxAdd.doubled() |> Nx.to_flat_list()
# [2, 4]
```

---

## Layout

```
agda/Muro.agda          public re-export
agda/Muro/Base.agda     Qty, Mode, Use, Result
agda/Muro/Syntax.agda   Tm n, PTm V
agda/Muro/Subst.agda    wk, sub, toPHOAS, unembed
agda/Muro/Check.agda    ⊢ and the decision procedure
agda/Muro/Example.agda  plus / IsEven / half / plus_suc / half_ok
agda/Muro/ExampleStream.agda  zeros / head-zeros
agda/Muro/ExampleEither.agda  IsEven / Dec / evenDec
agda/Muro/ExampleList.agda  length / ones2
agda/Muro/ExampleVec.agda   Fin / Vec / lookup
agda/Muro/ExampleNx.agda    addI / addT / t1
lib/muro/parser.ex      .muro → named FOAS
lib/muro/ast.ex         named FOAS, to_db
lib/muro/subst.ex       de Bruijn subst
lib/muro/check.ex       Elixir mirror of ⊢
lib/muro/emit.ex        run → Elixir source
lib/muro/example.ex     same book as Agda
lib/mix/tasks/muro.check.ex
examples/half_ok.muro
examples/internal_ok.muro
examples/zeros.muro
examples/nats.muro
examples/always.muro
examples/even_dec.muro
examples/either_run.muro
examples/list.muro
examples/maybe.muro
examples/tree.muro
examples/vec.muro
examples/nx_add.muro
test/muro_check_test.exs
```

---

## Build

Agda 2.8+ and standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` is `agda --no-libraries -i agda -i vendor/agda-stdlib/src` (the stdlib checkout ships extra `.agda-lib` files that must not be loaded).

Elixir 1.20.4 and OTP 29.1 via [mise](https://mise.jdx.dev/):

```
mise install
mix deps.get
mix test
mix muro.check
mix muro.check examples/half_ok.muro
```

`Muro.Check.check_sig/1` returns `:ok` on the book. CI runs the Elixir job and `make agda` on every push and pull request.

---

## Names

| | |
| --- | --- |
| Language | Muro |
| Theory | MuroTT |
| Files | `.muro` |
| Elixir | `Muro`, `Muro.Check`, `Muro.Emit`, `Muro.Parser` |
| Agda | `Muro.*` |

## Not in v1

Type : Type, cubical, tactics, implicits, unification, metavariables, extra quantities, user-defined ν-predicates, `+` on Stream or Either, typing raw Elixir, emitting spec or evidence.
