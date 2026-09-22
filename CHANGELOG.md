# Changelog

## 0.2.0

- Conversion in ⊢ is the relation `≈` from `Muro.Convert`. `Muro.Judgement`, `Muro.Wall`, and `Muro.Consistency` are checked under `--safe`. No closed normal evidence term has type Empty. `Empty-evid` itself is not proved.
- Kinds are not small types. `Π (x : A) → Type` is well-formed and is not a term of type `Type`, in Agda and in Elixir.

## 0.1.0

First release on Hex, owned by the `murolang` organization. MIT.

- `Muro.Lexer` returns byte spans for a fragment. `Muro.MakeupLexer` maps those spans to Makeup tags.
