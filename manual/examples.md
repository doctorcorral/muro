---
title: Examples
slug: examples
order: 13
summary: Every file in examples/ and what it is for.
---

# Examples

In brief: every file below checks with `mix muro.check path`. They are the worked book, not sketches. Prefer copying from here over inventing syntax.

Check one file:

```
mix muro.check examples/half_ok.muro
```

Check the built-in book (must match `half_ok.muro`):

```
mix muro.check
```

## half_ok.muro

The three modes in one book.

```
IsEven : Nat → Type                 -- spec
half   : Nat → Nat                  -- run
half_ok : (n : Nat) → IsEven n →    -- evidence
            plus (half n) (half n) ≡ n
```

Also defines `plus` (run) and `plus_suc` (evidence). Half of eight is four. Evidence is `match` + `refl` + `rewrite` + `matchEmpty`. Nothing here except `plus` and `half` is emitted.

See [The wall](wall.md), [Terms](language.md), [Identity](identity.md).

## internal_ok.muro

`run internal` helper `step` emits `defp`. `inc` is `run` and calls it. See [Emit](emit.md).

## zeros.muro

A productive `run` Stream of zeros. `head-zeros` is `{head zeros ≡ 0 : Nat}` by `refl`.

## nats.muro

`natsFrom n` is the stream `n, suc n, …`. Emit is `Stream.unfold/2`. `(+ k : Nat)` is legal because Nat is Data.

## always.muro

`Always` as evidence: every head of `zeros` satisfies `{0 ≡ 0 : Nat}`.

## bisim.muro

`zeros ~ zeros'` and `tail (natsFrom n) ~ natsFrom (suc n)`. Rutten’s stream calculus, Theorem 2.1. Evidence only.

See [Streams](streams.md).

## even_dec.muro

`Dec P = P ⊎ (P → Empty)`. `evenDec` decides `IsEven n`. A decision, not LEM. Evidence; not emitted.

## either_run.muro

A `run` sum. `fromLeft` emits `{:left, _}` / `{:right, _}`.

See [Either and Dec](either.md).

## list.muro

`List A`, `nil` / `cons`, `length`, `ones2`. `List A` is Data iff `A` is. `length-ones2` is `refl`.

## maybe.muro

`Maybe`, `fromMaybe`, `fromJust1`. Erased type argument.

## tree.muro

Binary trees of structure (no payloads). `size` descends on both children.

## vec.muro

`Fin n`, `Vec A n`, `lookup` without a runtime bounds check. `lookup-ok` is `refl`.

See [Data](data.md) and [Indexed data](indexed.md).

## nx_add.muro

`I64` and `Tensor`. `doubled` is `[2, 4]` after `Nx.to_flat_list/1`. Nat stays Peano.

See [Machine numbers](machine.md).

## Adding a file

1. Put it in `examples/`. Use only `run` / `run internal` / `spec` / `evidence`.
2. Every binder is `(x : A)` or `(+ x : A)` or `(- x : A)`.
3. Every `match` / `rewrite` writes `motive (λ x → …)` in parentheses.
4. Recursion on `run`/`evidence` goes through `match` and a smaller variable.
5. `mix muro.check examples/your_file.muro`.
6. If it belongs in CI, add parse/check/emit in `test/muro_check_test.exs`.

Do not edit Agda or `lib/muro/*.ex` to make a program work. If the program is allowed by the grammar and the checker refuses a term that should check, that is a kernel bug — a different job. See [For agents](for-agents.md).
