------------------------------------------------------------------------
-- Declarative typing for the ⊢ fragment, without uses. This is the
-- judgment the metatheory is about.
--
--   σ , Γ ⊨[ m ] e ∶ A   is   σ , Γ ⊨⁰[ m ] e ∶ A₀  with  σ ⊢[ spec ] A₀ ≈ A
--
-- Conversion sits at the root of every rule and nowhere else, so
-- inversion is pattern matching (conv D c). The rules of ⊨⁰ are those
-- of Muro.Judgement with use vectors, checkBound and combine removed,
-- and the Π / ≡ views folded into the premises. Uses restrict which
-- terms are accepted; they do not change what a term's type is, so the
-- consistency argument can forget them (forget-⇐).
--
-- Proved here:
--   forget-⇒ / forget-⇐   ⊢ is sound for ⊨
--   ⊨-mode                mode weakening along run ≤ evid ≤ spec
--   ⊨-ren                 renaming (contexts related pointwise by Ren)
--   ⊨-sub / ⊨-inst        substitution
--   pres / pres*          preservation: a ⟶ step, taken in any mode,
--                         keeps the type of a run- or evid-mode
--                         derivation, given a signature whose bodies
--                         have their declared types (WfSig)
--
-- Why not spec mode: rwt reads its equation in evid whatever the
-- surrounding mode is. A spec-mode λ may therefore bind a variable that
-- is used as evidence, and the spec-typed argument that β substitutes
-- for it would have to be evidence. Every other premise is in a mode
-- ≥ the mode of its conclusion. This is a design point, not a proof
-- gap; see the manual.
--
-- Why not ⊢ itself: ann e A ⟶ e removes the annotation a bidirectional
-- derivation needs (rwt rfl P t has no ⇒ derivation since rfl only
-- checks). Preservation of ⊢ up to re-annotation is not attempted.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Typing where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base as Vec using ([]; _∷_; lookup; map)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env
open import Muro.Reduction
open import Muro.Convert
open import Muro.Judgement

------------------------------------------------------------------------
-- Variables: which qty may be used in which mode.
------------------------------------------------------------------------

data VarOk : Mode → Qty → Set where
  v-spec : ∀ {q} → VarOk spec q
  v-run  : ∀ {q} → (q ≡ erased → ⊥) → VarOk run q
  v-evid : ∀ {q} → (q ≡ erased → ⊥) → VarOk evid q

VarOk-mono : ∀ {m m′ q} → m ≤ᵐ m′ → VarOk m q → VarOk m′ q
VarOk-mono {m′ = run}  ≤ᵐ-run (v-run h) = v-run h
VarOk-mono {m′ = evid} ≤ᵐ-run (v-run h) = v-evid h
VarOk-mono {m′ = spec} ≤ᵐ-run (v-run h) = v-spec
VarOk-mono ≤ᵐ-evid v = v
VarOk-mono ≤ᵐ-evsp _ = v-spec
VarOk-mono ≤ᵐ-spec v = v

------------------------------------------------------------------------
-- The judgment.
------------------------------------------------------------------------

infix 3 _,_⊨[_]_∶_ _,_⊨⁰[_]_∶_ _,_⊨_wf

data _,_⊨⁰[_]_∶_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊨[_]_∶_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊨_wf (σ : Sig) {n} (Γ : Ctx n) : Tm n → Set

data _,_⊨[_]_∶_ σ Γ where
  conv : ∀ {m e A B}
    → σ , Γ ⊨⁰[ m ] e ∶ A
    → σ ⊢[ spec ] A ≈ B
    → σ , Γ ⊨[ m ] e ∶ B

data _,_⊨_wf σ Γ where
  wf-typ : σ , Γ ⊨ typ wf
  wf-pi  : ∀ {q A B} → σ , Γ ⊨ A wf → σ , ext Γ q A ⊨ B wf → σ , Γ ⊨ pi q A B wf
  wf-el  : ∀ {A} → σ , Γ ⊨[ spec ] A ∶ typ → σ , Γ ⊨ A wf

data _,_⊨⁰[_]_∶_ σ Γ where
  t-var : ∀ {m x}
    → VarOk m (qtyOf Γ x)
    → σ , Γ ⊨⁰[ m ] var x ∶ typOf Γ x

  t-ze  : ∀ {m} → σ , Γ ⊨⁰[ m ] ze ∶ nat
  t-su  : ∀ {m t} → σ , Γ ⊨[ m ] t ∶ nat → σ , Γ ⊨⁰[ m ] su t ∶ nat
  t-one : ∀ {m} → σ , Γ ⊨⁰[ m ] one ∶ unit

  t-nat   : σ , Γ ⊨⁰[ spec ] nat   ∶ typ
  t-unit  : σ , Γ ⊨⁰[ spec ] unit  ∶ typ
  t-empty : σ , Γ ⊨⁰[ spec ] empty ∶ typ

  t-pi : ∀ {q A B}
    → σ , Γ ⊨ A wf
    → σ , ext Γ q A ⊨[ spec ] B ∶ typ
    → σ , Γ ⊨⁰[ spec ] pi q A B ∶ typ

  -- The binder type A is converted to the domain A′ the body is typed
  -- under (⇐-lam of ⊢; ⇒-lam is the case A′ = A).
  t-lam : ∀ {m q A A′ t B}
    → σ , Γ ⊨ A wf
    → σ ⊢[ spec ] A ≈ A′
    → reuseOk q A′ ≡ true
    → σ , ext Γ q A′ ⊨[ m ] t ∶ B
    → σ , Γ ⊨⁰[ m ] lam q A t ∶ pi q A′ B

  t-app-aff : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi affine A B
    → σ , Γ ⊨[ m ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-app-era : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi erased A B
    → σ , Γ ⊨[ spec ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-app-reuse : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi reuse A B
    → isDataF A ≡ true
    → σ , Γ ⊨[ m ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-idt : ∀ {A a b}
    → σ , Γ ⊨ A wf
    → σ , Γ ⊨[ spec ] a ∶ A
    → σ , Γ ⊨[ spec ] b ∶ A
    → σ , Γ ⊨⁰[ spec ] idt A a b ∶ typ

  t-rfl : ∀ {m A a b}
    → σ ⊢[ spec ] a ≈ b
    → σ , Γ ⊨⁰[ m ] rfl ∶ idt A a b

  t-rwt : ∀ {m eq A l r P t}
    → σ , Γ ⊨[ evid ] eq ∶ idt A l r
    → σ , ext Γ affine A ⊨ P wf
    → σ , Γ ⊨[ m ] t ∶ inst P r
    → σ , Γ ⊨⁰[ m ] rwt eq P t ∶ inst P l

  t-mNat : ∀ {m e P z s}
    → σ , Γ ⊨[ m ] e ∶ nat
    → σ , ext Γ affine nat ⊨ P wf
    → σ , Γ ⊨[ m ] z ∶ inst P ze
    → σ , ext Γ affine nat ⊨[ m ] s ∶ motSuc P
    → σ , Γ ⊨⁰[ m ] mNat e P z s ∶ inst P e

  t-mEmp : ∀ {m e P}
    → σ , Γ ⊨[ m ] e ∶ empty
    → σ , ext Γ affine empty ⊨ P wf
    → σ , Γ ⊨⁰[ m ] mEmp e P ∶ inst P e

  t-mUnit : ∀ {m e P u}
    → σ , Γ ⊨[ m ] e ∶ unit
    → σ , ext Γ affine unit ⊨ P wf
    → σ , Γ ⊨[ m ] u ∶ inst P one
    → σ , Γ ⊨⁰[ m ] mUnit e P u ∶ inst P e

  t-def : ∀ {m i d}
    → lookupDef σ i ≡ ok d
    → allowedDef (Def.dmode d) m ≡ true
    → σ , Γ ⊨⁰[ m ] def i ∶ closed (Def.dtype d)

  t-ann : ∀ {m e A}
    → σ , Γ ⊨ A wf
    → σ , Γ ⊨[ m ] e ∶ A
    → σ , Γ ⊨⁰[ m ] ann e A ∶ A

-- Conversion composes.
conv-≈ : ∀ {σ n} {Γ : Ctx n} {m e A B}
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ spec ] A ≈ B → σ , Γ ⊨[ m ] e ∶ B
conv-≈ (conv D c) c′ = conv D (≈-trans c c′)

≈-≡ : ∀ {σ m n} {A B : Tm n} → A ≡ B → σ ⊢[ m ] A ≈ B
≈-≡ refl = ≈-refl

⊨-≡ : ∀ {σ n} {Γ : Ctx n} {m e A B}
  → A ≡ B → σ , Γ ⊨[ m ] e ∶ A → σ , Γ ⊨[ m ] e ∶ B
⊨-≡ refl D = D

------------------------------------------------------------------------
-- ⊢ is sound for ⊨: forget the uses.
------------------------------------------------------------------------

forget-⇒ : ∀ {σ n} {Γ : Ctx n} {m e A u}
  → σ , Γ ⊢[ m ] e ⇒ A ⊣ u → σ , Γ ⊨[ m ] e ∶ A
forget-⇐ : ∀ {σ n} {Γ : Ctx n} {m e A u}
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u → σ , Γ ⊨[ m ] e ∶ A
forget-wf : ∀ {σ n} {Γ : Ctx n} {A}
  → σ , Γ ⊢ A wf → σ , Γ ⊨ A wf

forget-⇒ (⇒-var-run h) = conv (t-var (v-run h)) ≈-refl
forget-⇒ (⇒-var-evid h) = conv (t-var (v-evid h)) ≈-refl
forget-⇒ ⇒-var-spec = conv (t-var v-spec) ≈-refl
forget-⇒ ⇒-ze = conv t-ze ≈-refl
forget-⇒ (⇒-su D) = conv (t-su (forget-⇐ D)) ≈-refl
forget-⇒ ⇒-one = conv t-one ≈-refl
forget-⇒ ⇒-nat = conv t-nat ≈-refl
forget-⇒ ⇒-unit = conv t-unit ≈-refl
forget-⇒ ⇒-empty = conv t-empty ≈-refl
forget-⇒ (⇒-pi W D) = conv (t-pi (forget-wf W) (forget-⇐ D)) ≈-refl
forget-⇒ (⇒-lam W rok D _) =
  conv (t-lam (forget-wf W) ≈-refl rok (forget-⇒ D)) ≈-refl
forget-⇒ (⇒-app-aff Df c Da _) =
  conv (t-app-aff (conv-≈ (forget-⇒ Df) c) (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-app-era Df c Da) =
  conv (t-app-era (conv-≈ (forget-⇒ Df) c) (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-app-reuse Df c isd Da _) =
  conv (t-app-reuse (conv-≈ (forget-⇒ Df) c) isd (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-idt W Da Db) =
  conv (t-idt (forget-wf W) (forget-⇐ Da) (forget-⇐ Db)) ≈-refl
forget-⇒ (⇒-rwt Deq c W Dt) =
  conv (t-rwt (conv-≈ (forget-⇒ Deq) c) (forget-wf W) (forget-⇐ Dt)) ≈-refl
forget-⇒ (⇒-mNat De W Dz Ds _ _) =
  conv (t-mNat (forget-⇐ De) (forget-wf W) (forget-⇐ Dz) (forget-⇐ Ds)) ≈-refl
forget-⇒ (⇒-mEmp De W) = conv (t-mEmp (forget-⇐ De) (forget-wf W)) ≈-refl
forget-⇒ (⇒-mUnit De W Du _) =
  conv (t-mUnit (forget-⇐ De) (forget-wf W) (forget-⇐ Du)) ≈-refl
forget-⇒ (⇒-def lk al) = conv (t-def lk al) ≈-refl
forget-⇒ (⇒-ann W D) = conv (t-ann (forget-wf W) (forget-⇐ D)) ≈-refl

forget-⇐ (⇐-conv D c) = conv-≈ (forget-⇒ D) c
forget-⇐ (⇐-lam W c rok D _) =
  conv (t-lam (forget-wf W) c rok (forget-⇐ D)) ≈-refl
forget-⇐ (⇐-refl c) = conv (t-rfl c) ≈-refl

forget-wf type-Type = wf-typ
forget-wf (type-pi WA WB) = wf-pi (forget-wf WA) (forget-wf WB)
forget-wf (type-el D) = wf-el (forget-⇒ D)

------------------------------------------------------------------------
-- Mode weakening.
------------------------------------------------------------------------

⊨-mode : ∀ {σ n} {Γ : Ctx n} {m m′ e A}
  → m ≤ᵐ m′ → σ , Γ ⊨[ m ] e ∶ A → σ , Γ ⊨[ m′ ] e ∶ A
⊨⁰-mode : ∀ {σ n} {Γ : Ctx n} {m m′ e A}
  → m ≤ᵐ m′ → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Γ ⊨⁰[ m′ ] e ∶ A

⊨-mode h (conv D c) = conv (⊨⁰-mode h D) c

⊨⁰-mode h (t-var v) = t-var (VarOk-mono h v)
⊨⁰-mode h t-ze = t-ze
⊨⁰-mode h (t-su D) = t-su (⊨-mode h D)
⊨⁰-mode h t-one = t-one
⊨⁰-mode ≤ᵐ-spec t-nat = t-nat
⊨⁰-mode ≤ᵐ-spec t-unit = t-unit
⊨⁰-mode ≤ᵐ-spec t-empty = t-empty
⊨⁰-mode ≤ᵐ-spec (t-pi W D) = t-pi W D
⊨⁰-mode h (t-lam W c rok D) = t-lam W c rok (⊨-mode h D)
⊨⁰-mode h (t-app-aff Df Da) = t-app-aff (⊨-mode h Df) (⊨-mode h Da)
⊨⁰-mode h (t-app-era Df Da) = t-app-era (⊨-mode h Df) Da
⊨⁰-mode h (t-app-reuse Df isd Da) = t-app-reuse (⊨-mode h Df) isd (⊨-mode h Da)
⊨⁰-mode ≤ᵐ-spec (t-idt W Da Db) = t-idt W Da Db
⊨⁰-mode h (t-rfl c) = t-rfl c
⊨⁰-mode h (t-rwt Deq W Dt) = t-rwt Deq W (⊨-mode h Dt)
⊨⁰-mode h (t-mNat De W Dz Ds) = t-mNat (⊨-mode h De) W (⊨-mode h Dz) (⊨-mode h Ds)
⊨⁰-mode h (t-mEmp De W) = t-mEmp (⊨-mode h De) W
⊨⁰-mode h (t-mUnit De W Du) = t-mUnit (⊨-mode h De) W (⊨-mode h Du)
⊨⁰-mode h (t-def {d = d} lk al) = t-def lk (allowedDef-mono (Def.dmode d) h al)
⊨⁰-mode h (t-ann W D) = t-ann W (⊨-mode h D)

------------------------------------------------------------------------
-- Contexts: lookup under ext.
------------------------------------------------------------------------

qty-ext-suc : ∀ {n} (Γ : Ctx n) q A (x : Fin n)
  → qtyOf (ext Γ q A) (suc x) ≡ qtyOf Γ x
qty-ext-suc Γ q A x rewrite lookup-map x wkBind Γ = refl

typ-ext-suc : ∀ {n} (Γ : Ctx n) q A (x : Fin n)
  → typOf (ext Γ q A) (suc x) ≡ wk (typOf Γ x)
typ-ext-suc Γ q A x rewrite lookup-map x wkBind Γ = refl

------------------------------------------------------------------------
-- Data types are fixed by renaming and substitution.
------------------------------------------------------------------------

data IsData {n} : Tm n → Set where
  d-nat   : IsData nat
  d-unit  : IsData unit
  d-empty : IsData empty

isData? : ∀ {n} (A : Tm n) → isDataF A ≡ true → IsData A
isData? nat _ = d-nat
isData? unit _ = d-unit
isData? empty _ = d-empty
isData? (var _) ()
isData? typ ()
isData? (pi _ _ _) ()
isData? (lam _ _ _) ()
isData? (app _ _) ()
isData? ze ()
isData? (su _) ()
isData? one ()
isData? (dty _) ()
isData? (ctor _ _) ()
isData? (mData _ _ _) ()
isData? (mNat _ _ _ _) ()
isData? (mEmp _ _) ()
isData? (mUnit _ _ _) ()
isData? (idt _ _ _) ()
isData? rfl ()
isData? (rwt _ _ _) ()
isData? (def _) ()
isData? (ann _ _) ()
isData? (prod _ _) ()
isData? (pair _ _) ()
isData? (fst _) ()
isData? (snd _) ()
isData? (nu _) ()
isData? (unf _ _) ()
isData? (ucons _) ()
isData? i64 ()
isData? f32ty ()
isData? (tensor _ _) ()
isData? (addi _ _) ()
isData? (muli _ _) ()
isData? (addt _ _) ()
isData? (toi64 _) ()
isData? (packi _ _) ()

isDataF-ren : ∀ {n k} (ρ : Fin n → Fin k) {A : Tm n}
  → isDataF A ≡ true → isDataF (ren ρ A) ≡ true
isDataF-ren ρ {A} h with isData? A h
... | d-nat = refl
... | d-unit = refl
... | d-empty = refl

isDataF-sub : ∀ {n k} (τ : Fin n → Tm k) {A : Tm n}
  → isDataF A ≡ true → isDataF (sub τ A) ≡ true
isDataF-sub τ {A} h with isData? A h
... | d-nat = refl
... | d-unit = refl
... | d-empty = refl

reuseOk-ren : ∀ {n k} (ρ : Fin n → Fin k) q {A : Tm n}
  → reuseOk q A ≡ true → reuseOk q (ren ρ A) ≡ true
reuseOk-ren ρ affine h = refl
reuseOk-ren ρ erased h = refl
reuseOk-ren ρ reuse h = isDataF-ren ρ h

reuseOk-sub : ∀ {n k} (τ : Fin n → Tm k) q {A : Tm n}
  → reuseOk q A ≡ true → reuseOk q (sub τ A) ≡ true
reuseOk-sub τ affine h = refl
reuseOk-sub τ erased h = refl
reuseOk-sub τ reuse h = isDataF-sub τ h

------------------------------------------------------------------------
-- Renaming. Γ renames into Δ along ρ when qtys agree and types are
-- renamed.
------------------------------------------------------------------------

Ren : ∀ {n k} → (Fin n → Fin k) → Ctx n → Ctx k → Set
Ren ρ Γ Δ = ∀ x → (qtyOf Δ (ρ x) ≡ qtyOf Γ x) × (typOf Δ (ρ x) ≡ ren ρ (typOf Γ x))

Ren-lift : ∀ {n k} {ρ : Fin n → Fin k} {Γ Δ}
  → Ren ρ Γ Δ → ∀ q A → Ren (lift ρ) (ext Γ q A) (ext Δ q (ren ρ A))
Ren-lift {ρ = ρ} r q A zero = refl , sym (ren-wk ρ A)
Ren-lift {ρ = ρ} {Γ} {Δ} r q A (suc x)
  rewrite qty-ext-suc Δ q (ren ρ A) (ρ x) | typ-ext-suc Δ q (ren ρ A) (ρ x)
        | qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | proj₂ (r x) =
  proj₁ (r x) , sym (ren-wk ρ (typOf Γ x))

-- Weakening by one binder.
Ren-wk : ∀ {n} (Γ : Ctx n) q A → Ren suc Γ (ext Γ q A)
Ren-wk Γ q A x = qty-ext-suc Γ q A x , typ-ext-suc Γ q A x

-- The empty context renames into any context.
Ren-closed : ∀ {n} (Γ : Ctx n) → Ren fromZero ε Γ
Ren-closed Γ ()

⊨-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m e A}
  → Ren ρ Γ Δ → σ , Γ ⊨[ m ] e ∶ A → σ , Δ ⊨[ m ] ren ρ e ∶ ren ρ A
⊨⁰-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m e A}
  → Ren ρ Γ Δ → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Δ ⊨⁰[ m ] ren ρ e ∶ ren ρ A
wf-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ A}
  → Ren ρ Γ Δ → σ , Γ ⊨ A wf → σ , Δ ⊨ ren ρ A wf

⊨-ren {ρ = ρ} r (conv D c) = conv (⊨⁰-ren r D) (≈-ren ρ c)

⊨⁰-ren {ρ = ρ} {Γ} {Δ} {m} r (t-var {x = x} v) with r x
... | eq , et =
  subst (λ T → _ , Δ ⊨⁰[ m ] var (ρ x) ∶ T) et
    (t-var (subst (VarOk m) (sym eq) v))
⊨⁰-ren r t-ze = t-ze
⊨⁰-ren r (t-su D) = t-su (⊨-ren r D)
⊨⁰-ren r t-one = t-one
⊨⁰-ren r t-nat = t-nat
⊨⁰-ren r t-unit = t-unit
⊨⁰-ren r t-empty = t-empty
⊨⁰-ren r (t-pi W D) = t-pi (wf-ren r W) (⊨-ren (Ren-lift r _ _) D)
⊨⁰-ren {ρ = ρ} r (t-lam {q = q} W c rok D) =
  t-lam (wf-ren r W) (≈-ren ρ c) (reuseOk-ren ρ q rok) (⊨-ren (Ren-lift r _ _) D)
⊨⁰-ren {ρ = ρ} r (t-app-aff {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-aff (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-era {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-era (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-reuse {a = a} {B = B} Df isd Da) rewrite ren-inst ρ B a =
  t-app-reuse (⊨-ren r Df) (isDataF-ren ρ isd) (⊨-ren r Da)
⊨⁰-ren r (t-idt W Da Db) = t-idt (wf-ren r W) (⊨-ren r Da) (⊨-ren r Db)
⊨⁰-ren {ρ = ρ} r (t-rfl c) = t-rfl (≈-ren ρ c)
⊨⁰-ren {ρ = ρ} r (t-rwt {l = l} {r = r′} {P = P} Deq W Dt) rewrite ren-inst ρ P l =
  t-rwt (⊨-ren r Deq) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P r′) (⊨-ren r Dt))
⊨⁰-ren {ρ = ρ} r (t-mNat {e = e} {P = P} De W Dz Ds) rewrite ren-inst ρ P e =
  t-mNat (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P ze) (⊨-ren r Dz))
    (⊨-≡ (ren-motSuc ρ P) (⊨-ren (Ren-lift r _ _) Ds))
⊨⁰-ren {ρ = ρ} r (t-mEmp {e = e} {P = P} De W) rewrite ren-inst ρ P e =
  t-mEmp (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
⊨⁰-ren {ρ = ρ} r (t-mUnit {e = e} {P = P} De W Du) rewrite ren-inst ρ P e =
  t-mUnit (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P one) (⊨-ren r Du))
⊨⁰-ren {ρ = ρ} r (t-def {d = d} lk al) rewrite closed-ren ρ (Def.dtype d) = t-def lk al
⊨⁰-ren r (t-ann W D) = t-ann (wf-ren r W) (⊨-ren r D)

wf-ren r wf-typ = wf-typ
wf-ren r (wf-pi WA WB) = wf-pi (wf-ren r WA) (wf-ren (Ren-lift r _ _) WB)
wf-ren r (wf-el D) = wf-el (⊨-ren r D)

-- A closed derivation holds in any context.
closed-⊨ : ∀ {σ n} {Γ : Ctx n} {m e A}
  → σ , ε ⊨[ m ] e ∶ A → σ , Γ ⊨[ m ] closed e ∶ closed A
closed-⊨ {Γ = Γ} D = ⊨-ren (Ren-closed Γ) D

------------------------------------------------------------------------
-- Substitution. τ maps Γ into Δ when each τ x has the (substituted)
-- type of x, in mode m₀ if x is usable computationally and in spec if
-- x is erased. m₀ must be run or evid: see the header.
------------------------------------------------------------------------

modeFor : Qty → Mode → Mode
modeFor erased _ = spec
modeFor affine m = m
modeFor reuse  m = m

varOk-modeFor : ∀ q m₀ → VarOk (modeFor q m₀) q
varOk-modeFor erased m₀ = v-spec
varOk-modeFor affine run  = v-run (λ ())
varOk-modeFor affine evid = v-evid (λ ())
varOk-modeFor affine spec = v-spec
varOk-modeFor reuse  run  = v-run (λ ())
varOk-modeFor reuse  evid = v-evid (λ ())
varOk-modeFor reuse  spec = v-spec

-- A variable usable in mode m, substituted by a term in mode m₀ ≤ m.
modeFor-≤ : ∀ {m m₀ q} → VarOk m q → m₀ ≤ᵐ evid → m₀ ≤ᵐ m → modeFor q m₀ ≤ᵐ m
modeFor-≤ v-spec _ _ = ≤ᵐ-spec-top
modeFor-≤ {q = erased} (v-run h) _ _ = ⊥-elim (h refl)
modeFor-≤ {q = affine} (v-run h) _ lm = lm
modeFor-≤ {q = reuse}  (v-run h) _ lm = lm
modeFor-≤ {q = erased} (v-evid h) _ _ = ⊥-elim (h refl)
modeFor-≤ {q = affine} (v-evid h) le _ = le
modeFor-≤ {q = reuse}  (v-evid h) le _ = le

Subst : ∀ {n k} → Sig → Mode → (Fin n → Tm k) → Ctx n → Ctx k → Set
Subst σ m₀ τ Γ Δ = ∀ x → σ , Δ ⊨[ modeFor (qtyOf Γ x) m₀ ] τ x ∶ sub τ (typOf Γ x)

Subst-lifts : ∀ {σ n k m₀} {τ : Fin n → Tm k} {Γ Δ}
  → Subst σ m₀ τ Γ Δ → ∀ q A → Subst σ m₀ (lifts τ) (ext Γ q A) (ext Δ q (sub τ A))
Subst-lifts {m₀ = m₀} {τ} s q A zero =
  conv (t-var (varOk-modeFor q m₀)) (≈-≡ (sym (sub-wk τ A)))
Subst-lifts {τ = τ} {Γ} {Δ} s q A (suc x)
  rewrite qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | sub-wk τ (typOf Γ x) =
  ⊨-ren (Ren-wk Δ q (sub τ A)) (s x)

⊨-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ e A}
  → m₀ ≤ᵐ evid → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨[ m ] e ∶ A → σ , Δ ⊨[ m ] sub τ e ∶ sub τ A
⊨⁰-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ e A}
  → m₀ ≤ᵐ evid → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Δ ⊨[ m ] sub τ e ∶ sub τ A
wf-sub : ∀ {σ n k m₀} {τ : Fin n → Tm k} {Γ Δ A}
  → m₀ ≤ᵐ evid → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨ A wf → σ , Δ ⊨ sub τ A wf

⊨-sub {τ = τ} le lm s (conv D c) = conv-≈ (⊨⁰-sub le lm s D) (≈-sub τ c)

⊨⁰-sub le lm s (t-var {x = x} v) = ⊨-mode (modeFor-≤ v le lm) (s x)
⊨⁰-sub le lm s t-ze = conv t-ze ≈-refl
⊨⁰-sub le lm s (t-su D) = conv (t-su (⊨-sub le lm s D)) ≈-refl
⊨⁰-sub le lm s t-one = conv t-one ≈-refl
⊨⁰-sub le lm s t-nat = conv t-nat ≈-refl
⊨⁰-sub le lm s t-unit = conv t-unit ≈-refl
⊨⁰-sub le lm s t-empty = conv t-empty ≈-refl
⊨⁰-sub le lm s (t-pi W D) =
  conv (t-pi (wf-sub le s W) (⊨-sub le ≤ᵐ-spec-top (Subst-lifts s _ _) D)) ≈-refl
⊨⁰-sub {τ = τ} le lm s (t-lam {q = q} W c rok D) =
  conv (t-lam (wf-sub le s W) (≈-sub τ c) (reuseOk-sub τ q rok)
          (⊨-sub le lm (Subst-lifts s _ _) D)) ≈-refl
⊨⁰-sub {τ = τ} le lm s (t-app-aff {a = a} {B = B} Df Da) =
  conv (t-app-aff (⊨-sub le lm s Df) (⊨-sub le lm s Da)) (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} le lm s (t-app-era {a = a} {B = B} Df Da) =
  conv (t-app-era (⊨-sub le lm s Df) (⊨-sub le ≤ᵐ-spec-top s Da))
    (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} le lm s (t-app-reuse {a = a} {B = B} Df isd Da) =
  conv (t-app-reuse (⊨-sub le lm s Df) (isDataF-sub τ isd) (⊨-sub le lm s Da))
    (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub le lm s (t-idt W Da Db) =
  conv (t-idt (wf-sub le s W) (⊨-sub le ≤ᵐ-spec-top s Da) (⊨-sub le ≤ᵐ-spec-top s Db))
    ≈-refl
⊨⁰-sub {τ = τ} le lm s (t-rfl c) = conv (t-rfl (≈-sub τ c)) ≈-refl
⊨⁰-sub {τ = τ} le lm s (t-rwt {l = l} {r = r} {P = P} Deq W Dt) =
  conv (t-rwt (⊨-sub le le s Deq) (wf-sub le (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P r) (⊨-sub le lm s Dt)))
    (≈-≡ (sym (sub-inst τ P l)))
⊨⁰-sub {τ = τ} le lm s (t-mNat {e = e} {P = P} De W Dz Ds) =
  conv (t-mNat (⊨-sub le lm s De) (wf-sub le (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P ze) (⊨-sub le lm s Dz))
          (⊨-≡ (sub-motSuc τ P) (⊨-sub le lm (Subst-lifts s _ _) Ds)))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} le lm s (t-mEmp {e = e} {P = P} De W) =
  conv (t-mEmp (⊨-sub le lm s De) (wf-sub le (Subst-lifts s _ _) W))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} le lm s (t-mUnit {e = e} {P = P} De W Du) =
  conv (t-mUnit (⊨-sub le lm s De) (wf-sub le (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P one) (⊨-sub le lm s Du)))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} le lm s (t-def {d = d} lk al) =
  conv (t-def lk al) (≈-≡ (sym (closed-sub τ (Def.dtype d))))
⊨⁰-sub le lm s (t-ann W D) = conv (t-ann (wf-sub le s W) (⊨-sub le lm s D)) ≈-refl

wf-sub le s wf-typ = wf-typ
wf-sub le s (wf-pi WA WB) = wf-pi (wf-sub le s WA) (wf-sub le (Subst-lifts s _ _) WB)
wf-sub le s (wf-el D) = wf-el (⊨-sub le ≤ᵐ-spec-top s D)

-- Instantiating the last binder.
Subst-inst : ∀ {σ n m₀} {Γ : Ctx n} q A {a}
  → σ , Γ ⊨[ modeFor q m₀ ] a ∶ A
  → Subst σ m₀ (instσ a) (ext Γ q A) Γ
Subst-inst q A {a} Da zero = ⊨-≡ (sym (inst-wk A a)) Da
Subst-inst {m₀ = m₀} {Γ} q A {a} Da (suc x)
  rewrite qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | inst-wk (typOf Γ x) a =
  conv (t-var (varOk-modeFor (qtyOf Γ x) m₀)) ≈-refl

⊨-inst : ∀ {σ n m₀ m} {Γ : Ctx n} {q A t B a}
  → m₀ ≤ᵐ evid → m₀ ≤ᵐ m
  → σ , ext Γ q A ⊨[ m ] t ∶ B
  → σ , Γ ⊨[ modeFor q m₀ ] a ∶ A
  → σ , Γ ⊨[ m ] inst t a ∶ inst B a
⊨-inst {q = q} {A} le lm D Da = ⊨-sub le lm (Subst-inst q A Da) D

------------------------------------------------------------------------
-- Preservation.
------------------------------------------------------------------------

-- Every def body has its declared type, in its declared mode.
WfSig : Sig → Set
WfSig σ = ∀ i d → lookupDef σ i ≡ ok d
  → σ , ε ⊨[ Def.dmode d ] Def.dbody d ∶ Def.dtype d

WfSig-empty : WfSig σ-empty
WfSig-empty _ _ ()

allowedDef→≤ᵐ : ∀ d m → allowedDef d m ≡ true → d ≤ᵐ m
allowedDef→≤ᵐ run  _    _ = ≤ᵐ-run
allowedDef→≤ᵐ evid run  ()
allowedDef→≤ᵐ evid evid _ = ≤ᵐ-evid
allowedDef→≤ᵐ evid spec _ = ≤ᵐ-evsp
allowedDef→≤ᵐ spec run  ()
allowedDef→≤ᵐ spec evid ()
allowedDef→≤ᵐ spec spec _ = ≤ᵐ-spec

-- The step may be taken in any mode m′: δ is justified by the typing's
-- allowedDef, not the step's.
pres : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ → m ≤ᵐ evid
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶ e′ → σ , Γ ⊨[ m ] e′ ∶ A
pres⁰ : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ → m ≤ᵐ evid
  → σ , Γ ⊨⁰[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶ e′ → σ , Γ ⊨[ m ] e′ ∶ A

pres wf le (conv D c) s = conv-≈ (pres⁰ wf le D s) c

-- A step is a conversion (in spec mode, where every def unfolds).
step-≈ : ∀ {σ m n} {e e′ : Tm n} → σ ⊢[ m ] e ⟶ e′ → σ ⊢[ spec ] e′ ≈ e
step-≈ s = ≈-sym (≈-mode ≤ᵐ-spec-top (⟶→≈ s))

-- δ
pres⁰ wf le (t-def {d = d} lk al) (δ lk′ _) with ok-inj (trans (sym lk) lk′)
... | refl = ⊨-mode (allowedDef→≤ᵐ (Def.dmode d) _ al) (closed-⊨ (wf _ _ lk))
-- β
pres⁰ wf le (t-app-aff (conv (t-lam W c rok Dt) cpi) Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst le ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
pres⁰ wf le (t-app-era (conv (t-lam W c rok Dt) cpi) Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst le ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
pres⁰ wf le (t-app-reuse (conv (t-lam W c rok Dt) cpi) isd Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst le ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
-- congruence in the function
pres⁰ wf le (t-app-aff Df Da) (app-f s) = conv (t-app-aff (pres wf le Df s) Da) ≈-refl
pres⁰ wf le (t-app-era Df Da) (app-f s) = conv (t-app-era (pres wf le Df s) Da) ≈-refl
pres⁰ wf le (t-app-reuse Df isd Da) (app-f s) =
  conv (t-app-reuse (pres wf le Df s) isd Da) ≈-refl
-- ι
pres⁰ wf le (t-mNat De W Dz Ds) ιz = Dz
pres⁰ wf le (t-mNat {P = P} (conv (t-su Du) _) W Dz Ds) (ιs {u = u}) =
  conv-≈ (⊨-inst le ≤ᵐ-refl Ds Du) (≈-≡ (inst-motSuc P u))
pres⁰ wf le (t-mNat {P = P} De W Dz Ds) (mNat-e s) =
  conv (t-mNat (pres wf le De s) W Dz Ds) (≈-inst P (step-≈ s))
pres⁰ wf le (t-mUnit De W Du) ιtt = Du
pres⁰ wf le (t-mUnit {P = P} De W Du) (mUnit-e s) =
  conv (t-mUnit (pres wf le De s) W Du) (≈-inst P (step-≈ s))
pres⁰ wf le (t-mEmp {P = P} De W) (mEmp-e s) =
  conv (t-mEmp (pres wf le De s) W) (≈-inst P (step-≈ s))
pres⁰ wf le (t-rwt {P = P} (conv (t-rfl cab) cid) W Dt) ιrfl with ≈-idt-inj cid
... | _ , cal , cbr =
  conv-≈ Dt (≈-inst P (≈-trans (≈-sym cbr) (≈-trans (≈-sym cab) cal)))
pres⁰ wf le (t-rwt Deq W Dt) (rwt-e s) =
  conv (t-rwt (pres wf ≤ᵐ-evid Deq s) W Dt) ≈-refl
-- ann
pres⁰ wf le (t-ann W D) ann-e = D
-- rigid forms do not step
pres⁰ wf le (t-var _) ()
pres⁰ wf le t-ze ()
pres⁰ wf le (t-su _) ()
pres⁰ wf le t-one ()
pres⁰ wf le t-nat ()
pres⁰ wf le t-unit ()
pres⁰ wf le t-empty ()
pres⁰ wf le (t-pi _ _) ()
pres⁰ wf le (t-lam _ _ _ _) ()
pres⁰ wf le (t-idt _ _ _) ()
pres⁰ wf le (t-rfl _) ()

pres* : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ → m ≤ᵐ evid
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶* e′ → σ , Γ ⊨[ m ] e′ ∶ A
pres* wf le D ⟶*-refl = D
pres* wf le D (⟶*-step s r) = pres* wf le (pres wf le D s) r
