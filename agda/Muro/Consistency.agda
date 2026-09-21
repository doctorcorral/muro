------------------------------------------------------------------------
-- Closed evidence of Empty, on the ⊢ fragment, under --safe.
--
-- Proved here, with conversion the relation ≈ of Muro.Convert:
--
--   Empty-intro      an introduction form (ze, su, one, λ, refl) never
--                    checks against Empty, in any σ, Γ, and mode;
--   Empty-nf         no closed normal evidence term has type Empty
--                    (canonical evidence forms at Empty do not exist);
--   progress-⇐       a closed well-typed evidence term is normal or
--                    takes a ⟶ step;
--   Empty-evid-from  preservation and normalisation of closed evidence
--                    together give: no closed evidence of Empty. Both
--                    hypotheses are arguments of the lemma. Nothing is
--                    postulated.
--
-- Not proved: Empty-evid itself. What is missing is exactly the two
-- hypotheses of Empty-evid-from.
--   * Preservation needs the substitution lemma for ⊢ with uses (β
--     substitutes the argument into the body and its type).
--   * Normalisation of closed evidence terms. Type is impredicative
--     (Π (X : Type) → X : Type), so a set-theoretic model in Agda is
--     not available; the argument must be syntactic, and for evid it
--     can use that evid is affine outside Data.
-- Do not cite Empty-evid as a theorem of this development.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Consistency where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Env
open import Muro.Convert
open import Muro.Judgement

fail≢ok : ∀ {A : Set} {e} {d : A} → fail e ≡ ok d → ⊥
fail≢ok ()

------------------------------------------------------------------------
-- The term `empty` is spec-only.
------------------------------------------------------------------------

no-evid-empty-⇒ : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] empty ⇒ A ⊣ u → ⊥
no-evid-empty-⇒ ()

no-evid-empty-⇐ : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] empty ⇐ A ⊣ u → ⊥
no-evid-empty-⇐ (⇐-conv D _) = no-evid-empty-⇒ D

------------------------------------------------------------------------
-- Introduction forms are never evidence of Empty: they infer a canonical
-- type former other than Empty, and ≈ separates distinct normal forms.
------------------------------------------------------------------------

data Intro {n} : Tm n → Set where
  i-ze  : Intro ze
  i-su  : ∀ {t} → Intro (su t)
  i-one : Intro one
  i-lam : ∀ {q A t} → Intro (lam q A t)
  i-rfl : Intro rfl

Empty-intro-⇒ : ∀ {σ n} {Γ : Ctx n} {m e B u} →
  Intro e → σ , Γ ⊢[ m ] e ⇒ B ⊣ u → σ ⊢[ m ] B ≈ empty → ⊥
Empty-intro-⇒ i-ze ⇒-ze c with ≈-nf nf-nat nf-empty c
... | ()
Empty-intro-⇒ i-su (⇒-su _) c with ≈-nf nf-nat nf-empty c
... | ()
Empty-intro-⇒ i-one ⇒-one c with ≈-nf nf-unit nf-empty c
... | ()
Empty-intro-⇒ i-lam (⇒-lam _ _ _ _) c with ≈-nf nf-pi nf-empty c
... | ()
Empty-intro-⇒ i-rfl () _

Empty-intro : ∀ {σ n} {Γ : Ctx n} {m e u} →
  Intro e → σ , Γ ⊢[ m ] e ⇐ empty ⊣ u → ⊥
Empty-intro i (⇐-conv D c) = Empty-intro-⇒ i D c

------------------------------------------------------------------------
-- Closed neutral terms are not evidence: there is no variable, no
-- definition in σ-empty, and no ⊢ rule for terms outside the fragment.
------------------------------------------------------------------------

ne-untyped-⇒ : ∀ {e B u} →
  Ne σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇒ B ⊣ u → ⊥
ne-untyped-⇐ : ∀ {e A u} →
  Ne σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ A ⊣ u → ⊥

ne-untyped-⇒ (ne-var {x = ()}) _
ne-untyped-⇒ (ne-def _) (⇒-def lk _) = fail≢ok lk
ne-untyped-⇒ (ne-app ne _) (⇒-app-aff D _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-app ne _) (⇒-app-era D _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-app ne _) (⇒-app-reuse D _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-mNat ne) (⇒-mNat D _ _ _ _ _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-mUnit ne) (⇒-mUnit D _ _ _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-mEmp ne) (⇒-mEmp D _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-rwt ne) (⇒-rwt D _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-foreign f-dty) ()
ne-untyped-⇒ (ne-foreign f-ctor) ()
ne-untyped-⇒ (ne-foreign f-mData) ()
ne-untyped-⇒ (ne-foreign f-prod) ()
ne-untyped-⇒ (ne-foreign f-pair) ()
ne-untyped-⇒ (ne-foreign f-fst) ()
ne-untyped-⇒ (ne-foreign f-snd) ()
ne-untyped-⇒ (ne-foreign f-nu) ()
ne-untyped-⇒ (ne-foreign f-unf) ()
ne-untyped-⇒ (ne-foreign f-ucons) ()
ne-untyped-⇒ (ne-foreign f-i64) ()
ne-untyped-⇒ (ne-foreign f-f32ty) ()
ne-untyped-⇒ (ne-foreign f-tensor) ()
ne-untyped-⇒ (ne-foreign f-addi) ()
ne-untyped-⇒ (ne-foreign f-muli) ()
ne-untyped-⇒ (ne-foreign f-addt) ()
ne-untyped-⇒ (ne-foreign f-toi64) ()
ne-untyped-⇒ (ne-foreign f-packi) ()

ne-untyped-⇐ ne (⇐-conv D _) = ne-untyped-⇒ ne D
ne-untyped-⇐ (ne-foreign ()) (⇐-lam _ _ _ _ _)
ne-untyped-⇐ (ne-foreign ()) (⇐-refl _)

------------------------------------------------------------------------
-- No closed normal evidence of Empty.
------------------------------------------------------------------------

Empty-nf : ∀ {e u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
Empty-nf (nf-ne ne) D = ne-untyped-⇐ ne D
Empty-nf nf-typ (⇐-conv () _)
Empty-nf nf-pi (⇐-conv () _)
Empty-nf nf-lam D = Empty-intro i-lam D
Empty-nf nf-nat (⇐-conv () _)
Empty-nf nf-ze D = Empty-intro i-ze D
Empty-nf (nf-su _) D = Empty-intro i-su D
Empty-nf nf-unit (⇐-conv () _)
Empty-nf nf-one D = Empty-intro i-one D
Empty-nf nf-empty D = no-evid-empty-⇐ D
Empty-nf nf-idt (⇐-conv () _)
Empty-nf nf-rfl D = Empty-intro i-rfl D

------------------------------------------------------------------------
-- Progress: a closed well-typed evidence term is normal or steps.
------------------------------------------------------------------------

Step : Tm 0 → Set
Step e = ∃ λ e′ → σ-empty ⊢[ evid ] e ⟶ e′

Prog : Tm 0 → Set
Prog e = Nf σ-empty evid e ⊎ Step e

data IsLam {n} : Tm n → Set where
  is-lam : ∀ {q A t} → IsLam (lam q A t)

-- Canonical forms, for normal closed evidence at each type former.

nf-fun : ∀ {f F q A B u} →
  Nf σ-empty evid f → σ-empty , ε ⊢[ evid ] f ⇒ F ⊣ u →
  σ-empty ⊢[ evid ] F ≈ pi q A B → IsLam f
nf-fun (nf-ne ne) D _ = ⊥-elim (ne-untyped-⇒ ne D)
nf-fun nf-lam _ _ = is-lam
nf-fun nf-ze ⇒-ze c with ≈-nf nf-nat nf-pi c
... | ()
nf-fun (nf-su _) (⇒-su _) c with ≈-nf nf-nat nf-pi c
... | ()
nf-fun nf-one ⇒-one c with ≈-nf nf-unit nf-pi c
... | ()
nf-fun nf-typ () _
nf-fun nf-pi () _
nf-fun nf-nat () _
nf-fun nf-unit () _
nf-fun nf-empty () _
nf-fun nf-idt () _
nf-fun nf-rfl () _

nf-nat-prog : ∀ {e P z s u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ nat ⊣ u →
  Prog (mNat e P z s)
nf-nat-prog (nf-ne ne) D = ⊥-elim (ne-untyped-⇐ ne D)
nf-nat-prog nf-ze _ = inj₂ (_ , ιz)
nf-nat-prog (nf-su _) _ = inj₂ (_ , ιs)
nf-nat-prog nf-lam (⇐-conv (⇒-lam _ _ _ _) c) with ≈-nf nf-pi nf-nat c
... | ()
nf-nat-prog nf-one (⇐-conv ⇒-one c) with ≈-nf nf-unit nf-nat c
... | ()
nf-nat-prog nf-typ (⇐-conv () _)
nf-nat-prog nf-pi (⇐-conv () _)
nf-nat-prog nf-nat (⇐-conv () _)
nf-nat-prog nf-unit (⇐-conv () _)
nf-nat-prog nf-empty (⇐-conv () _)
nf-nat-prog nf-idt (⇐-conv () _)
nf-nat-prog nf-rfl (⇐-conv () _)

nf-unit-prog : ∀ {e P t u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ unit ⊣ u →
  Prog (mUnit e P t)
nf-unit-prog (nf-ne ne) D = ⊥-elim (ne-untyped-⇐ ne D)
nf-unit-prog nf-one _ = inj₂ (_ , ιtt)
nf-unit-prog nf-ze (⇐-conv ⇒-ze c) with ≈-nf nf-nat nf-unit c
... | ()
nf-unit-prog (nf-su _) (⇐-conv (⇒-su _) c) with ≈-nf nf-nat nf-unit c
... | ()
nf-unit-prog nf-lam (⇐-conv (⇒-lam _ _ _ _) c) with ≈-nf nf-pi nf-unit c
... | ()
nf-unit-prog nf-typ (⇐-conv () _)
nf-unit-prog nf-pi (⇐-conv () _)
nf-unit-prog nf-nat (⇐-conv () _)
nf-unit-prog nf-unit (⇐-conv () _)
nf-unit-prog nf-empty (⇐-conv () _)
nf-unit-prog nf-idt (⇐-conv () _)
nf-unit-prog nf-rfl (⇐-conv () _)

nf-eq-prog : ∀ {eq E A l r P t u} →
  Nf σ-empty evid eq → σ-empty , ε ⊢[ evid ] eq ⇒ E ⊣ u →
  σ-empty ⊢[ evid ] E ≈ idt A l r → Prog (rwt eq P t)
nf-eq-prog (nf-ne ne) D _ = ⊥-elim (ne-untyped-⇒ ne D)
nf-eq-prog nf-rfl _ _ = inj₂ (_ , ιrfl)
nf-eq-prog nf-ze ⇒-ze c with ≈-nf nf-nat nf-idt c
... | ()
nf-eq-prog (nf-su _) (⇒-su _) c with ≈-nf nf-nat nf-idt c
... | ()
nf-eq-prog nf-one ⇒-one c with ≈-nf nf-unit nf-idt c
... | ()
nf-eq-prog nf-lam (⇒-lam _ _ _ _) c with ≈-nf nf-pi nf-idt c
... | ()
nf-eq-prog nf-typ () _
nf-eq-prog nf-pi () _
nf-eq-prog nf-nat () _
nf-eq-prog nf-unit () _
nf-eq-prog nf-empty () _
nf-eq-prog nf-idt () _

progress-⇒ : ∀ {e B u} → σ-empty , ε ⊢[ evid ] e ⇒ B ⊣ u → Prog e
progress-⇐ : ∀ {e A u} → σ-empty , ε ⊢[ evid ] e ⇐ A ⊣ u → Prog e

progress-⇐ (⇐-conv D _) = progress-⇒ D
progress-⇐ (⇐-lam _ _ _ _ _) = inj₁ nf-lam
progress-⇐ (⇐-refl _) = inj₁ nf-rfl

progress-⇒ (⇒-var-evid {x = ()} _)
progress-⇒ ⇒-ze = inj₁ nf-ze
progress-⇒ (⇒-su D) with progress-⇐ D
... | inj₁ nf = inj₁ (nf-su nf)
... | inj₂ (_ , s) = inj₂ (_ , su-c s)
progress-⇒ ⇒-one = inj₁ nf-one
progress-⇒ (⇒-lam _ _ _ _) = inj₁ nf-lam
progress-⇒ (⇒-app-aff Df c _ _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-app-era Df c _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-app-reuse Df c _ _ _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-rwt Deq c _ _) with progress-⇒ Deq
... | inj₂ (_ , s) = inj₂ (_ , rwt-e s)
... | inj₁ nf = nf-eq-prog nf Deq c
progress-⇒ (⇒-mNat De _ _ _ _ _) with progress-⇐ De
... | inj₁ nf = nf-nat-prog nf De
... | inj₂ (_ , s) with step-natCanon s
...   | inj₁ nc = inj₂ (_ , mNat-e nc s)
...   | inj₂ (_ , refl) = inj₂ (_ , ιs)
progress-⇒ (⇒-mEmp De _) with progress-⇐ De
... | inj₁ nf = ⊥-elim (Empty-nf nf De)
... | inj₂ (_ , s) = inj₂ (_ , mEmp-e s)
progress-⇒ (⇒-mUnit De _ _ _) with progress-⇐ De
... | inj₁ nf = nf-unit-prog nf De
... | inj₂ (_ , s) = inj₂ (_ , mUnit-e s)
progress-⇒ (⇒-def lk _) = ⊥-elim (fail≢ok lk)
progress-⇒ (⇒-ann _ _) = inj₂ (_ , ann-e)

------------------------------------------------------------------------
-- The remaining obligations, as hypotheses. Not postulated.
------------------------------------------------------------------------

-- Preservation: a ⟶ step keeps closed evidence at Empty.
Preservation : Set
Preservation = ∀ {e e′ u} →
  σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u →
  σ-empty ⊢[ evid ] e ⟶ e′ →
  σ-empty , ε ⊢[ evid ] e′ ⇐ empty ⊣ u

-- Normalisation: closed evidence at Empty reaches a normal form.
Normalising : Set
Normalising = ∀ {e u} →
  σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u →
  ∃ λ v → (σ-empty ⊢[ evid ] e ⟶* v) × Nf σ-empty evid v

Empty-evid-from : Preservation → Normalising →
  ∀ {e u} → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
Empty-evid-from pres norm D with norm D
... | v , r , nf = Empty-nf nf (pres* r D)
  where
    pres* : ∀ {e v u} →
      σ-empty ⊢[ evid ] e ⟶* v →
      σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u →
      σ-empty , ε ⊢[ evid ] v ⇐ empty ⊣ u
    pres* ⟶*-refl D′ = D′
    pres* (⟶*-step s r′) D′ = pres* r′ (pres D′ s)
