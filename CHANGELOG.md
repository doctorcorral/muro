# Changelog

## 0.3.0

The checker changes. Each change makes `Muro.Check` agree with ⊢ where they disagreed; the disagreements were found by proving the checker sound. All shipped examples check as before.

### Checker (`Muro.Check`, `mix muro.check`)

- A type is recognised by its shape. `checkTy` no longer reduces first: `Type` and `Π (x : A) → K` are kinds as written, anything else must infer a type convertible to `Type`. Refused now, accepted before: a term that merely reduces to `Type` or to a kind used as a type, such as `(λ (x : Nat) → Type) 0`. Error text: `Type has no type`.
- Arguments at a call site of an evidence definition are checked in the mode of the application. Inside an evidence term, `lem a` with `lem` an evidence definition checks `a` in `evidence` (before: in `spec`) and then discards its uses, so instantiating a theorem still consumes nothing. Refused now, accepted before: passing a spec variable to a theorem from an evidence term (`no promotion`).
- `isData` is fuelled, like every other loop over `whnf`: a recursive spec definition (`X : Type := D X`) at a `+` binder now fails with `+ requires a Data type` instead of not returning.

### Agda (`agda/Muro`)

- `Muro.Soundness`: the executable checker is sound for ⊢ on the fragment. Over a `GoodSig` (a fragment signature whose data types are non-indexed and whose constructor types are telescopes ending in the data type) and a fragment context, `infer k σ rs Γ m e ≡ ok (A , u)` gives `σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u` with `A′ ≈ A` (`infer-sound`), `check … ≡ ok u` gives `⊢[ m ] e ⇐ A ⊣ u` (`check-sound`), `checkTy … ≡ ok tt` gives `⊢ A wf` (`checkTy-sound`); `checkDef-sound` and `checkSig-sound` are the corollaries for definitions and whole signatures. On the way: `whnf-sound` (`Check.whnf` is `⟶*` in spec and preserves the fragment), `synEq-sound`, `conv-sound` (`Check.conv` says yes → `≈`), `isData-sound`, `instParams-sound`, the spine views, and the `match` path (`checkBr-sound`, `checkBranches-sound`). The proof is by structural recursion on a depth-indexed fragment predicate (`FragD`). One direction only, for every fuel; the module imports `Muro.Check` and is therefore not `--safe`.
- `Muro.Frag` (the ⊢ fragment as a predicate on terms, lists, signatures, and contexts, closed under renaming and substitution) and `Muro.Tag` (constructor tags) are new and `--safe`. `Muro.Spine` gains the spine views `Check` uses (`ctorSpine`, `dtyArgs`, `defArgs`, `lamView`) with their characterisations.
- ⊢ reads types through `≈` wherever `Check` reads them through `whnf`: `type-el` (a type is a spec term whose sort is convertible to `Type`), `⇐-lam` and `⇐-refl` (the expected type is convertible to a Π / an identity type), `⇐-ctor` (constructor spine as a `Spine`, arguments along the instantiated telescope by the list judgment `T ▹ as ⇝ R`, replacing `ctor⟨ di , ps ⟩⇝`). `⇐-≈`: ⇐ is closed under conversion of the type. `⇒-app-aff` / `⇒-app-reuse` take their uses from `Env.appUses`.
- `Muro.Check`: `synEq` and `convN` compare constructor tags before structure; `defArgs`, `dtyArgs`, `ctorSpine`, `lamView` are the `Muro.Spine` views; `forcePairs`, `checkAgainst`, `checkTy` are in the form the proof follows; `infer′` takes the term before the mode (so that Agda's case tree splits on the term first). Behaviour unchanged except as listed under Checker.
- `Makefile`: `agda-safe` also checks `Muro.Frag` and `Muro.Tag`; new target `agda-soundness`.

### Manual

- `wall.md`, `identity.md`: the argument at an evidence call site is checked in evidence, its uses discarded. `limits.md`, `extending.md`, `for-agents.md`, README: what `Muro.Soundness` proves and does not, the new modules, and the three checker clauses the proof corrected.

### Package

- Version 0.3.0. `agda/Muro.agda` re-exports `Muro.Frag`, `Muro.Tag`, `Muro.Soundness`.

## 0.2.2

No checker change. Every book that checked under 0.2.1 checks under 0.2.2 with the same result. Agda and manual only.

### Agda (`agda/Muro`)

- `data` is in ⊢. `Muro.Judgement` has `⇒-dty` (a data former is a spec term of its declared kind), `⇐-ctor` (a constructor application checked against a `dty` type: parameters from the type, arguments along the instantiated telescope, an erased field in spec, as `Check.checkCtorApp`), and `⇒-mData` (`match` on a non-indexed data type: the motive at the scrutinee, one branch per constructor in declaration order, each of the type `BrTy` gives, as `Check.checkBranches`). Two auxiliary judgments carry the spine (`ctor⟨ di , ps ⟩⇝`) and the branches (`brs⟨ … ⟩`). `Muro.Env` gains `fieldMode` and `combineArg` (the mode and the uses of a constructor argument).
- Preservation covers ι for `match`. `Muro.Typing` types a constructor spine as one rule (`t-ctor`, with `ctor-inv` its inversion), `match` by `t-mData`, and proves `pres` for `ι-data`: the branch for the constructor applied to the constructor's arguments has the motive at the scrutinee (`brApp`). The proof needs nothing of the data declarations beyond what the derivations carry. Mode weakening, renaming, substitution, and `forget-⇐` extend to the new rules.
- Reduction knows `match`. `Muro.Reduction` has `⇛-ιdata` and the complete development of `mData` on a constructor spine; confluence is re-proved with it. `Muro.Convert` has `ι-data` and `mData-e` in `⟶` (exactly `Check.dataWhnf`), constructor and `dty` spines as normal forms, `≈L` on argument lists, `≈-dty-inj`, and the separation of constructor spines from `dty` spines and rigid heads.
- `Muro.Spine` (application spines as a relation, unique for rigid heads) and `Muro.Data` (`IsData`, `ReuseOk`, `InstParams`, `BrTy`, each closed under renaming, substitution, and conversion) are new. `IsData` is σ-relative and covers `dty` spines whose parameters are Data, as `Check.isData`; `reuse` binders and applications use it in ⊢ and ⊨.
- `Muro.Wall`: `no-run-dty` / `no-evid-dty`; spec derivations still carry zero uses through the new rules.
- `Muro.Consistency`: `σ-empty` declares no data type, so constructor and `dty` spines are untyped in it; `Empty-nf`, progress, and `Empty-nf⊨` cover the new normal forms. `Empty-evid-from` is unchanged: normalisation of closed evidence remains the one hypothesis.
- Still outside ⊢: `match` on an indexed data type (forced indices), ν, Tensor. ⊢ does not check `data` declarations (`Check.checkData`: positivity, small fields).

### Manual

- `extending.md`, `limits.md`, `for-agents.md`, README: the fragment now includes `data`; the new modules and what a rule whose subject is a variable costs.

### Package

- Version 0.2.2. `agda/Muro.agda` re-exports `Muro.Spine` and `Muro.Data`.

## 0.2.1

No checker change. Every book that checked under 0.2.0 checks under 0.2.1 with the same result. Agda and manual only.

### Agda (`agda/Muro`)

- Preservation is a theorem. `Muro.Typing` defines the declarative judgment `⊨` (⊢ without uses, conversion at the root of every rule) and proves: ⊢ is sound for `⊨` (`forget-⇐`), mode weakening along run ≤ evid ≤ spec, renaming, substitution (`⊨-sub`, `⊨-inst`), and `pres`: a `⟶` step, taken in any mode, keeps the type of a run- or evidence-mode derivation over a signature whose bodies have their declared types. `Muro.Consistency.Empty-evid-from` now takes only `Normalising`; `preservation` is the specialised corollary at `σ-empty`.
- Conversion is congruent. `Muro.Reduction` defines parallel reduction `⇛` (δ, β, ι, `ann`, congruent under every constructor of `Tm`), closed under substitution, confluent by complete developments (triangle property). `≈` in `Muro.Convert` is the equivalence generated by `⇛`, so it is closed under substitution and joinability comes from confluence, not from determinism of a strategy. Inversion is by rigid head (`≈-shape`) and Π / ≡ are injective up to `≈`. `Muro.SubstLemmas` holds the renaming / substitution algebra.
- `⟶` is exactly the `Check.whnf` strategy: the congruences in an application argument and under `suc` are gone (they served only the old `≈-nf` inversion).
- ⊢ takes conversion in spec mode, so every def unfolds during conversion, as `Check.whnf` does. Before, ⊢ could not check an evidence term whose type mentions a spec def although `Check` accepts it.
- `Muro.Env`: the mode order `≤ᵐ` (run ≤ evid ≤ spec) with `allowedDef` monotone.
- Recorded, not changed: the equation of a `rewrite` is checked in evidence whatever the surrounding mode is, so positions are not monotone in the mode inside spec terms and preservation is not claimed for spec derivations.

### Manual

- `extending.md`: the new modules, what each step of the order must add to them, and the two mode facts the metatheory depends on.
- `limits.md`, `for-agents.md`, README: what is proved now.

### Package

- Version 0.2.1. `agda/Muro.agda` re-exports the new modules.

## 0.2.0

The checker changes. A book that checked under 0.1.0 still checks unless it used a kind as a small type; all shipped examples are unchanged.

### Checker (`Muro.Check`, `mix muro.check`)

- Kinds are not small types. `Type` and `Π (x : A) → K` with `K` a kind are well-formed and may be the type of a `def`, a binder domain, a motive, or the sort of an identity type, but they are not terms of type `Type`. Refused now, accepted before: `Π (_ : Unit) → Type` where a term of type `Type` is expected, `Type × A`, and a `data` constructor field of type `Type` (parameters `(A : Type)` are exempt). Each of these made `Type` a retract of a small type, and with β or a `Type` motive that is Girard's paradox in `spec`. The premises that moved from well-formed to `: Type`: the codomain of `Π`, both components of `×`, the body of `ν` (kernel only; the surface ν is `Stream`), and constructor fields.
- Error text for these cases is `Type has no type (no Type : Type)`, tagged with the def or constructor.

### Agda (`agda/Muro`)

- Conversion in ⊢ is a relation. `Muro.Convert` defines deterministic weak-head reduction `⟶` (δ, β, ι for `Nat` / `Unit` / `Empty` / `rewrite`, congruence under `suc`, in the function and argument of an application, and in eliminator scrutinees) and `≈` as its equivalence closure, without fuel. `⇐-conv`, `⇐-lam`, `⇐-refl`, and the `Π` / `≡` views of `Muro.Judgement` use `≈` instead of `_≡_`. `≈` does not reduce under `λ`, `Π`, identity types, motives, or branches. `≈-nf`: distinct normal forms are not convertible.
- `Muro.Judgement`: `wf` has `type-pi`; `⇒-pi` checks the codomain against `Type`. `⇒-var-run` and `⇒-var-evid` were mis-parenthesised (two premises instead of `(qtyOf Γ x ≡ erased → ⊥)`) and no run or evidence variable was derivable; fixed.
- `Muro.Consistency`: the `Empty-evid` postulate is deleted. Proved: introduction forms never check against `Empty`; no closed normal evidence term has type `Empty`; closed neutral terms are untyped in the empty context; closed well-typed evidence terms are normal or take a `⟶` step. `Empty-evid-from : Preservation → Normalising → … → ⊥` states what remains. `Empty-evid` itself is not proved.
- `make agda` checks `Muro.Judgement`, `Muro.Wall`, `Muro.Consistency`, and their imports under `--safe`, then the whole tree. `Muro.Env` (signature, context, uses) and `Muro.Unembed` (PHOAS to de Bruijn, `TERMINATING`) are split out of `Muro.Check` and `Muro.Subst` so the theorem modules have no `TERMINATING` dependency. There are no postulates in `agda/`.
- data, ν, and Tensor are still outside ⊢.

### Manual

- `language.md`: small types versus kinds; `Type` is impredicative by design.
- `limits.md`: the refused retracts; the `⇒-pi` bug is recorded as fixed.
- `data.md`: constructor fields are small.
- `extending.md`: `Muro.Judgement` / `Muro.Convert` are a step of the order; the premises that keep the sort consistent, including why `⇒-idt` keeps a kind as its sort.
- `for-agents.md`: file map covers every Agda module and marks which are not `--safe`.

### Package

- Version 0.2.0. `CHANGELOG.md` ships in the Hex package. README points at Hex.

## 0.1.0

First release on Hex, owned by the `murolang` organization. MIT.

- `Muro.Lexer` returns byte spans for a fragment. `Muro.MakeupLexer` maps those spans to Makeup tags.
