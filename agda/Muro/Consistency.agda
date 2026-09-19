------------------------------------------------------------------------
-- Closed evidence of Empty.
--
-- Empty-core is proved: a Core term (no app, rewrite, or def) has no
-- evidence derivation of Empty in the empty signature and context.
--
-- Empty-evid is the full statement on ⊢. It is not proved in this pass
-- (application / rewrite / canonicity). Do not cite it as a theorem.
------------------------------------------------------------------------

module Muro.Consistency where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check using (Ctx; UseVec; lookupDef)
open import Muro.Judgement

------------------------------------------------------------------------
-- inst B a ≡ empty means B is empty, or B is var 0 and a is empty.
------------------------------------------------------------------------

inst-empty : ∀ {n} (B : Tm (suc n)) (a : Tm n) →
  inst B a ≡ empty → (B ≡ empty) ⊎ ((B ≡ var zero) × (a ≡ empty))
inst-empty (var zero)    a eq = inj₂ (refl , eq)
inst-empty (var (suc _)) _ ()
inst-empty typ           _ ()
inst-empty (pi _ _ _)    _ ()
inst-empty (lam _ _ _)   _ ()
inst-empty (app _ _)     _ ()
inst-empty nat           _ ()
inst-empty ze            _ ()
inst-empty (su _)        _ ()
inst-empty unit          _ ()
inst-empty one           _ ()
inst-empty empty         _ refl = inj₁ refl
inst-empty (dty _)       _ ()
inst-empty (ctor _ _)    _ ()
inst-empty (mData _ _ _) _ ()
inst-empty (mNat _ _ _ _) _ ()
inst-empty (mEmp _ _)    _ ()
inst-empty (mUnit _ _ _) _ ()
inst-empty (idt _ _ _)   _ ()
inst-empty rfl           _ ()
inst-empty (rwt _ _ _)   _ ()
inst-empty (def _)       _ ()
inst-empty (ann _ _)     _ ()
inst-empty (prod _ _)    _ ()
inst-empty (pair _ _)    _ ()
inst-empty (fst _)       _ ()
inst-empty (snd _)       _ ()
inst-empty (nu _)        _ ()
inst-empty (unf _ _)     _ ()
inst-empty (ucons _)     _ ()
inst-empty i64           _ ()
inst-empty f32ty         _ ()
inst-empty (tensor _ _)  _ ()
inst-empty (addi _ _)    _ ()
inst-empty (muli _ _)    _ ()
inst-empty (addt _ _)    _ ()
inst-empty (toi64 _)     _ ()
inst-empty (packi _ _)   _ ()

------------------------------------------------------------------------
-- Core terms: the fragment of ⊢ without app, rewrite, or def.
------------------------------------------------------------------------

data Core {n} : Tm n → Set where
  c-var  : ∀ {x} → Core (var x)
  c-ze   : Core ze
  c-su   : ∀ {t} → Core t → Core (su t)
  c-one  : Core one
  c-lam  : ∀ {q A t} → Core t → Core (lam q A t)
  c-mNat : ∀ {e P z s} → Core e → Core z → Core s → Core (mNat e P z s)
  c-mEmp : ∀ {e P} → Core e → Core (mEmp e P)
  c-mUnit : ∀ {e P tu} → Core e → Core tu → Core (mUnit e P tu)
  c-ann  : ∀ {e A} → Core e → Core (ann e A)
  c-rfl  : Core rfl
  c-empty : Core empty
  c-nat  : Core nat
  c-unit : Core unit
  c-pi   : ∀ {q A B} → Core A → Core B → Core (pi q A B)
  c-idt  : ∀ {A a b} → Core A → Core a → Core b → Core (idt A a b)

------------------------------------------------------------------------
-- The term `empty` is not evidence (⇒-empty is spec-only).
------------------------------------------------------------------------

no-evid-term-empty-⇒ : ∀ {n} {Γ : Ctx n} {A u} →
  σ-empty , Γ ⊢[ evid ] empty ⇒ A ⊣ u → ⊥
no-evid-term-empty-⇒ ()

no-evid-term-empty-⇐ : ∀ {n} {Γ : Ctx n} {A u} →
  σ-empty , Γ ⊢[ evid ] empty ⇐ A ⊣ u → ⊥
no-evid-term-empty-⇐ (⇐-conv D _) = no-evid-term-empty-⇒ D

------------------------------------------------------------------------
-- Empty-core: Core evidence of Empty, empty signature, empty context.
------------------------------------------------------------------------

mutual
  core-⇒ : ∀ {e A u} →
    Core e →
    σ-empty , ε ⊢[ evid ] e ⇒ A ⊣ u →
    A ≡ empty → ⊥
  core-⇐ : ∀ {e u} →
    Core e →
    σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥

  core-⇐ Ce (⇐-conv D refl) = core-⇒ Ce D refl

  core-⇒ {e = var x} c-var _ _ = noFin0 x
    where
      noFin0 : ∀ {A : Set} → Fin 0 → A
      noFin0 ()
  core-⇒ c-ze ⇒-ze ()
  core-⇒ (c-su _) (⇒-su _) ()
  core-⇒ c-one ⇒-one ()
  core-⇒ (c-lam _) (⇒-lam _ _ _ _) ()
  core-⇒ c-rfl () _
  core-⇒ c-empty D _ = no-evid-term-empty-⇒ D
  core-⇒ c-nat () _
  core-⇒ c-unit () _
  core-⇒ (c-pi _ _) () _
  core-⇒ (c-idt _ _ _) () _

  core-⇒ (c-ann Ce) (⇒-ann _ D) refl = core-⇐ Ce D

  core-⇒ (c-mEmp Ce) (⇒-mEmp D _) _ = core-⇐ Ce D

  core-⇒ (c-mUnit Ce Ctu) (⇒-mUnit {e = e} {P = P} De _ Dtu _) eq
    with inst-empty P e eq
  ... | inj₁ refl = core-⇐ Ctu Dtu
  ... | inj₂ (refl , refl) = no-evid-term-empty-⇐ De

  core-⇒ (c-mNat Ce Cz Cs) (⇒-mNat {e = e} {P = P} De _ Dz _ _ _) eq
    with inst-empty P e eq
  ... | inj₁ refl = core-⇐ Cz Dz
  ... | inj₂ (refl , refl) = no-evid-term-empty-⇐ De

Empty-core : ∀ {e u} → Core e → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
Empty-core = core-⇐

------------------------------------------------------------------------
-- Full statement. Not proved here (app / rewrite / canonicity).
-- POSTULATE: evidence Empty uninhabited (canonicity)
------------------------------------------------------------------------

postulate
  Empty-evid : ∀ {e u} → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
