------------------------------------------------------------------------
-- Closed evidence of Empty, on the ⊢ fragment.
--
-- Conversion is now the relation ≈ of Muro.Convert. Empty-intro is
-- proved: an introduction form never checks against Empty. Empty-evid
-- is still postulated here; it is discharged in the following commits.
------------------------------------------------------------------------

module Muro.Consistency where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Env
open import Muro.Convert
open import Muro.Judgement

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
-- Full statement. Not proved yet.
-- POSTULATE: evidence Empty uninhabited (canonicity)
------------------------------------------------------------------------

postulate
  Empty-evid : ∀ {e u} → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
