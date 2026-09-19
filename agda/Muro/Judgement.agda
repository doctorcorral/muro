------------------------------------------------------------------------
-- Inductive spec of MuroTT (core fragment).
--
-- fragment =
--   Type, Π/λ/app with Qty,
--   Nat / ze / su / mNat,
--   Empty / mEmp,
--   Unit / one / mUnit,
--   ≡ / refl / rewrite,
--   def lookup (allowedDef),
--   annotation,
--   uses as in Check (spec forgets; run/evid count).
--
-- omitted = data / ν / Tensor / I64 / F32 / products / pairs.
-- ⊢ does not track RecSt descent and does not use fuel.
-- Conversion is de Bruijn α-equality (Agda ≡), not fuelled WHNF.
-- Check.agda remains the executable spec of the full language.
------------------------------------------------------------------------

module Muro.Judgement where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List.Base as List using (List)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base using (ℕ; zero)
open import Data.Vec.Base as Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check
  using ( Sig; Def; mkSig; mkDef; lookupDef
        ; Ctx; Bind; bind; ext; qtyOf; typOf
        ; UseVec; u0s; oneHot; combine; combineAlt; checkBound
        ; allowedDef; addUse; addUses; motSuc )

------------------------------------------------------------------------
-- Data in this fragment: Nat, Unit, Empty. Closures are not Data.
------------------------------------------------------------------------

isDataF : ∀ {n} → Tm n → Bool
isDataF nat   = true
isDataF unit  = true
isDataF empty = true
isDataF _     = false

reuseOk : Qty → ∀ {n} → Tm n → Bool
reuseOk reuse A = isDataF A
reuseOk _     _ = true

------------------------------------------------------------------------
-- Conversion: α-equality of de Bruijn terms. No fuel, no WHNF.
------------------------------------------------------------------------

_≈_ : ∀ {n} → Tm n → Tm n → Set
_≈_ = _≡_

------------------------------------------------------------------------
-- Bidirectional ⊢. Uses sit in the conclusion (⊣).
------------------------------------------------------------------------

infix 3 _,_⊢[_]_⇒_⊣_ _,_⊢[_]_⇐_⊣_ _,_⊢_wf

data _,_⊢[_]_⇒_⊣_ (σ : Sig) {n} (Γ : Ctx n)
    : Mode → Tm n → Tm n → UseVec n → Set
data _,_⊢[_]_⇐_⊣_ (σ : Sig) {n} (Γ : Ctx n)
    : Mode → Tm n → Tm n → UseVec n → Set
data _,_⊢_wf (σ : Sig) {n} (Γ : Ctx n) : Tm n → Set

data _,_⊢_wf σ Γ where
  type-Type : σ , Γ ⊢ typ wf
  type-el   : ∀ {A u} → σ , Γ ⊢[ spec ] A ⇒ typ ⊣ u → σ , Γ ⊢ A wf

data _,_⊢[_]_⇒_⊣_ σ Γ where

  ⇒-var-run : ∀ {x}
    → qtyOf Γ x ≡ erased → ⊥
    → σ , Γ ⊢[ run ] var x ⇒ typOf Γ x
        ⊣ oneHot x (if eqQty (qtyOf Γ x) reuse then Uω else U1)

  ⇒-var-evid : ∀ {x}
    → qtyOf Γ x ≡ erased → ⊥
    → σ , Γ ⊢[ evid ] var x ⇒ typOf Γ x
        ⊣ oneHot x (if eqQty (qtyOf Γ x) reuse then Uω else U1)

  ⇒-var-spec : ∀ {x}
    → σ , Γ ⊢[ spec ] var x ⇒ typOf Γ x ⊣ u0s

  ⇒-ze : ∀ {m} → σ , Γ ⊢[ m ] ze ⇒ nat ⊣ u0s
  ⇒-su : ∀ {m t u} → σ , Γ ⊢[ m ] t ⇐ nat ⊣ u → σ , Γ ⊢[ m ] su t ⇒ nat ⊣ u
  ⇒-one : ∀ {m} → σ , Γ ⊢[ m ] one ⇒ unit ⊣ u0s

  ⇒-nat   : σ , Γ ⊢[ spec ] nat   ⇒ typ ⊣ u0s
  ⇒-unit  : σ , Γ ⊢[ spec ] unit  ⇒ typ ⊣ u0s
  ⇒-empty : σ , Γ ⊢[ spec ] empty ⇒ typ ⊣ u0s

  ⇒-pi : ∀ {q A B}
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢ B wf
    → σ , Γ ⊢[ spec ] pi q A B ⇒ typ ⊣ u0s

  ⇒-lam : ∀ {m q A t B u0 us}
    → σ , Γ ⊢ A wf
    → reuseOk q A ≡ true
    → σ , ext Γ q A ⊢[ m ] t ⇒ B ⊣ (u0 ∷ us)
    → checkBound m q u0 ≡ ok tt
    → σ , Γ ⊢[ m ] lam q A t ⇒ pi q A B ⊣ us

  ⇒-app-aff : ∀ {m A B f a fu au uses}
    → σ , Γ ⊢[ m ] f ⇒ pi affine A B ⊣ fu
    → σ , Γ ⊢[ m ] a ⇐ A ⊣ au
    → combine m fu au ≡ ok uses
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a ⊣ uses

  ⇒-app-era : ∀ {m A B f a fu au}
    → σ , Γ ⊢[ m ] f ⇒ pi erased A B ⊣ fu
    → σ , Γ ⊢[ spec ] a ⇐ A ⊣ au
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a ⊣ fu

  ⇒-app-reuse : ∀ {m A B f a fu au uses}
    → σ , Γ ⊢[ m ] f ⇒ pi reuse A B ⊣ fu
    → isDataF A ≡ true
    → σ , Γ ⊢[ m ] a ⇐ A ⊣ au
    → combine m fu au ≡ ok uses
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a ⊣ uses

  ⇒-idt : ∀ {A a b ua ub}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ spec ] a ⇐ A ⊣ ua
    → σ , Γ ⊢[ spec ] b ⇐ A ⊣ ub
    → σ , Γ ⊢[ spec ] idt A a b ⇒ typ ⊣ u0s

  -- Equality is evidence (as in infer′ of Check), uses discarded.
  ⇒-rwt : ∀ {m A l r eq P t eu tu}
    → σ , Γ ⊢[ evid ] eq ⇒ idt A l r ⊣ eu
    → σ , ext Γ affine A ⊢ P wf
    → σ , Γ ⊢[ m ] t ⇐ inst P r ⊣ tu
    → σ , Γ ⊢[ m ] rwt eq P t ⇒ inst P l ⊣ tu

  ⇒-mNat : ∀ {m e P z s eu zu u0 sus uses}
    → σ , Γ ⊢[ m ] e ⇐ nat ⊣ eu
    → σ , ext Γ affine nat ⊢ P wf
    → σ , Γ ⊢[ m ] z ⇐ inst P ze ⊣ zu
    → σ , ext Γ affine nat ⊢[ m ] s ⇐ motSuc P ⊣ (u0 ∷ sus)
    → checkBound m affine u0 ≡ ok tt
    → combine m eu (combineAlt m zu sus) ≡ ok uses
    → σ , Γ ⊢[ m ] mNat e P z s ⇒ inst P e ⊣ uses

  ⇒-mEmp : ∀ {m e P eu}
    → σ , Γ ⊢[ m ] e ⇐ empty ⊣ eu
    → σ , ext Γ affine empty ⊢ P wf
    → σ , Γ ⊢[ m ] mEmp e P ⇒ inst P e ⊣ eu

  ⇒-mUnit : ∀ {m e P tu eu uu uses}
    → σ , Γ ⊢[ m ] e ⇐ unit ⊣ eu
    → σ , ext Γ affine unit ⊢ P wf
    → σ , Γ ⊢[ m ] tu ⇐ inst P one ⊣ uu
    → combine m eu uu ≡ ok uses
    → σ , Γ ⊢[ m ] mUnit e P tu ⇒ inst P e ⊣ uses

  ⇒-def : ∀ {m i d}
    → lookupDef σ i ≡ ok d
    → allowedDef (Def.dmode d) m ≡ true
    → σ , Γ ⊢[ m ] def i ⇒ closed (Def.dtype d) ⊣ u0s

  ⇒-ann : ∀ {m e A u}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
    → σ , Γ ⊢[ m ] ann e A ⇒ A ⊣ u

data _,_⊢[_]_⇐_⊣_ σ Γ where
  ⇐-conv : ∀ {m e A B u}
    → σ , Γ ⊢[ m ] e ⇒ B ⊣ u
    → B ≈ A
    → σ , Γ ⊢[ m ] e ⇐ A ⊣ u

  ⇐-lam : ∀ {m q A A′ t B u0 us}
    → σ , Γ ⊢ A wf
    → A ≈ A′
    → reuseOk q A′ ≡ true
    → σ , ext Γ q A′ ⊢[ m ] t ⇐ B ⊣ (u0 ∷ us)
    → checkBound m q u0 ≡ ok tt
    → σ , Γ ⊢[ m ] lam q A t ⇐ pi q A′ B ⊣ us

  ⇐-refl : ∀ {m A a b}
    → a ≈ b
    → σ , Γ ⊢[ m ] rfl ⇐ idt A a b ⊣ u0s

------------------------------------------------------------------------
-- Empty signature / empty context (for Wall and Consistency).
------------------------------------------------------------------------

σ-empty : Sig
σ-empty = mkSig List.[] List.[]

ε : Ctx 0
ε = []
