------------------------------------------------------------------------
-- The ⊢ fragment as a predicate on terms: the constructors ⊢ has rules
-- for. The projections fst / snd, ν, unfold, I64 / F32 / Tensor are
-- outside. Closed
-- under renaming and substitution, so under everything Check.whnf does
-- to a fragment term over a fragment signature.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Frag where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Spine

data Frag {n} : Tm n → Set
data FragL {n} : List (Tm n) → Set

data Frag where
  f-var   : ∀ {x} → Frag (var x)
  f-typ   : Frag typ
  f-pi    : ∀ {q A B} → Frag A → Frag B → Frag (pi q A B)
  f-lam   : ∀ {q A t} → Frag A → Frag t → Frag (lam q A t)
  f-app   : ∀ {f a} → Frag f → Frag a → Frag (app f a)
  f-nat   : Frag nat
  f-ze    : Frag ze
  f-su    : ∀ {t} → Frag t → Frag (su t)
  f-unit  : Frag unit
  f-one   : Frag one
  f-empty : Frag empty
  f-dty   : ∀ {i} → Frag (dty i)
  f-ctor  : ∀ {i j} → Frag (ctor i j)
  f-mData : ∀ {e P bs} → Frag e → Frag P → FragL bs → Frag (mData e P bs)
  f-mNat  : ∀ {e P z s} → Frag e → Frag P → Frag z → Frag s → Frag (mNat e P z s)
  f-mEmp  : ∀ {e P} → Frag e → Frag P → Frag (mEmp e P)
  f-mUnit : ∀ {e P u} → Frag e → Frag P → Frag u → Frag (mUnit e P u)
  f-idt   : ∀ {A a b} → Frag A → Frag a → Frag b → Frag (idt A a b)
  f-rfl   : Frag rfl
  f-rwt   : ∀ {e P t} → Frag e → Frag P → Frag t → Frag (rwt e P t)
  f-def   : ∀ {i} → Frag (def i)
  f-ann   : ∀ {e A} → Frag e → Frag A → Frag (ann e A)
  f-prod  : ∀ {A B} → Frag A → Frag B → Frag (prod A B)
  f-pair  : ∀ {a b} → Frag a → Frag b → Frag (pair a b)
  f-letp  : ∀ {e t} → Frag e → Frag t → Frag (letp e t)

data FragL where
  fl-[] : FragL []
  fl-∷  : ∀ {t ts} → Frag t → FragL ts → FragL (t ∷ ts)

------------------------------------------------------------------------
-- Closure.
------------------------------------------------------------------------

Frag-ren : ∀ {n k} (ρ : Fin n → Fin k) {t : Tm n} → Frag t → Frag (ren ρ t)
FragL-ren : ∀ {n k} (ρ : Fin n → Fin k) {ts : List (Tm n)} → FragL ts → FragL (renList ρ ts)

Frag-ren ρ f-var = f-var
Frag-ren ρ f-typ = f-typ
Frag-ren ρ (f-pi A B) = f-pi (Frag-ren ρ A) (Frag-ren (lift ρ) B)
Frag-ren ρ (f-lam A t) = f-lam (Frag-ren ρ A) (Frag-ren (lift ρ) t)
Frag-ren ρ (f-app f a) = f-app (Frag-ren ρ f) (Frag-ren ρ a)
Frag-ren ρ f-nat = f-nat
Frag-ren ρ f-ze = f-ze
Frag-ren ρ (f-su t) = f-su (Frag-ren ρ t)
Frag-ren ρ f-unit = f-unit
Frag-ren ρ f-one = f-one
Frag-ren ρ f-empty = f-empty
Frag-ren ρ f-dty = f-dty
Frag-ren ρ f-ctor = f-ctor
Frag-ren ρ (f-mData e P bs) = f-mData (Frag-ren ρ e) (Frag-ren (lift ρ) P) (FragL-ren ρ bs)
Frag-ren ρ (f-mNat e P z s) =
  f-mNat (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ z) (Frag-ren (lift ρ) s)
Frag-ren ρ (f-mEmp e P) = f-mEmp (Frag-ren ρ e) (Frag-ren (lift ρ) P)
Frag-ren ρ (f-mUnit e P u) = f-mUnit (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ u)
Frag-ren ρ (f-idt A a b) = f-idt (Frag-ren ρ A) (Frag-ren ρ a) (Frag-ren ρ b)
Frag-ren ρ f-rfl = f-rfl
Frag-ren ρ (f-rwt e P t) = f-rwt (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ t)
Frag-ren ρ f-def = f-def
Frag-ren ρ (f-ann e A) = f-ann (Frag-ren ρ e) (Frag-ren ρ A)
Frag-ren ρ (f-prod A B) = f-prod (Frag-ren ρ A) (Frag-ren ρ B)
Frag-ren ρ (f-pair a b) = f-pair (Frag-ren ρ a) (Frag-ren ρ b)
Frag-ren ρ (f-letp e t) = f-letp (Frag-ren ρ e) (Frag-ren (lift (lift ρ)) t)

FragL-ren ρ fl-[] = fl-[]
FragL-ren ρ (fl-∷ t ts) = fl-∷ (Frag-ren ρ t) (FragL-ren ρ ts)

Frag-wk : ∀ {n} {t : Tm n} → Frag t → Frag (wk t)
Frag-wk = Frag-ren suc

Frag-closed : ∀ {n} {t : Tm 0} → Frag t → Frag (closed {n} t)
Frag-closed = Frag-ren fromZero

-- A substitution into the fragment.
FragS : ∀ {n k} → (Fin n → Tm k) → Set
FragS τ = ∀ x → Frag (τ x)

FragS-lifts : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → FragS (lifts τ)
FragS-lifts s zero = f-var
FragS-lifts s (suc x) = Frag-wk (s x)

Frag-sub : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → {t : Tm n} → Frag t → Frag (sub τ t)
FragL-sub : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → {ts : List (Tm n)} → FragL ts → FragL (subList τ ts)

Frag-sub s (f-var {x}) = s x
Frag-sub s f-typ = f-typ
Frag-sub s (f-pi A B) = f-pi (Frag-sub s A) (Frag-sub (FragS-lifts s) B)
Frag-sub s (f-lam A t) = f-lam (Frag-sub s A) (Frag-sub (FragS-lifts s) t)
Frag-sub s (f-app f a) = f-app (Frag-sub s f) (Frag-sub s a)
Frag-sub s f-nat = f-nat
Frag-sub s f-ze = f-ze
Frag-sub s (f-su t) = f-su (Frag-sub s t)
Frag-sub s f-unit = f-unit
Frag-sub s f-one = f-one
Frag-sub s f-empty = f-empty
Frag-sub s f-dty = f-dty
Frag-sub s f-ctor = f-ctor
Frag-sub s (f-mData e P bs) = f-mData (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (FragL-sub s bs)
Frag-sub s (f-mNat e P z s′) =
  f-mNat (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s z) (Frag-sub (FragS-lifts s) s′)
Frag-sub s (f-mEmp e P) = f-mEmp (Frag-sub s e) (Frag-sub (FragS-lifts s) P)
Frag-sub s (f-mUnit e P u) = f-mUnit (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s u)
Frag-sub s (f-idt A a b) = f-idt (Frag-sub s A) (Frag-sub s a) (Frag-sub s b)
Frag-sub s f-rfl = f-rfl
Frag-sub s (f-rwt e P t) = f-rwt (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s t)
Frag-sub s f-def = f-def
Frag-sub s (f-ann e A) = f-ann (Frag-sub s e) (Frag-sub s A)
Frag-sub s (f-prod A B) = f-prod (Frag-sub s A) (Frag-sub s B)
Frag-sub s (f-pair a b) = f-pair (Frag-sub s a) (Frag-sub s b)
Frag-sub s (f-letp e t) = f-letp (Frag-sub s e) (Frag-sub (FragS-lifts (FragS-lifts s)) t)

FragL-sub s fl-[] = fl-[]
FragL-sub s (fl-∷ t ts) = fl-∷ (Frag-sub s t) (FragL-sub s ts)

FragS-instσ : ∀ {n} {a : Tm n} → Frag a → FragS (instσ a)
FragS-instσ Fa zero = Fa
FragS-instσ Fa (suc x) = f-var

Frag-inst : ∀ {n} {t : Tm (ℕ.suc n)} {a} → Frag t → Frag a → Frag (inst t a)
Frag-inst Ft Fa = Frag-sub (FragS-instσ Fa) Ft

FragS-motSucσ : ∀ {n} → FragS (motSucσ {n})
FragS-motSucσ zero = f-su f-var
FragS-motSucσ (suc x) = f-var

Frag-motSuc : ∀ {n} {P : Tm (ℕ.suc n)} → Frag P → Frag (motSuc P)
Frag-motSuc = Frag-sub FragS-motSucσ

Frag-appsFrom : ∀ {n} {h : Tm n} {as} → Frag h → FragL as → Frag (appsFrom h as)
Frag-appsFrom Fh fl-[] = Fh
Frag-appsFrom Fh (fl-∷ Fa Fas) = Frag-appsFrom (f-app Fh Fa) Fas

FragL-++ : ∀ {n} {as bs : List (Tm n)} → FragL as → FragL bs → FragL (as ++ bs)
FragL-++ fl-[] G = G
FragL-++ (fl-∷ F Fs) G = fl-∷ F (FragL-++ Fs G)

-- Reading a spine off a fragment term.
Frag-Spine : ∀ {n} {h : Tm n} {as e} → Spine h as e → Frag e → Frag h × FragL as
Frag-Spine sp-[] Fe = Fe , fl-[]
Frag-Spine (sp-snoc sp) (f-app Ff Fa) with Frag-Spine sp Ff
... | Fh , Fas = Fh , FragL-++ Fas (fl-∷ Fa fl-[])

FragL-lookup : ∀ {n} {bs : List (Tm n)} {k b} → FragL bs → lookupList bs k ≡ ok b → Frag b
FragL-lookup {k = ℕ.zero} (fl-∷ F _) refl = F
FragL-lookup {k = ℕ.suc k} (fl-∷ _ Fs) eq = FragL-lookup Fs eq

------------------------------------------------------------------------
-- A signature in the fragment: every def type and body, every
-- constructor type, every index type.
------------------------------------------------------------------------

data FragIdxs : List (Qty × Tm 0) → Set where
  fi-[] : FragIdxs []
  fi-∷  : ∀ {q T ixs} → Frag T → FragIdxs ixs → FragIdxs ((q , T) ∷ ixs)

data FragCtors : List Ctor → Set where
  fc-[] : FragCtors []
  fc-∷  : ∀ {c cs} → Frag (Ctor.ctype c) → FragCtors cs → FragCtors (c ∷ cs)

record FragSig (σ : Sig) : Set where
  field
    defs  : ∀ i d → lookupDef σ i ≡ ok d → Frag (Def.dtype d) × Frag (Def.dbody d)
    datas : ∀ i d → lookupData σ i ≡ ok d → FragIdxs (DataDecl.idxs d) × FragCtors (DataDecl.ctors d)

FragCtors-lookup : ∀ {cs j c} → FragCtors cs → lookupList cs j ≡ ok c → Frag (Ctor.ctype c)
FragCtors-lookup {j = ℕ.zero} (fc-∷ F _) refl = F
FragCtors-lookup {j = ℕ.suc j} (fc-∷ _ Fs) eq = FragCtors-lookup Fs eq

Frag-dtyType : ∀ {n} qs {ixs} → FragIdxs ixs → Frag (dtyType {n} qs ixs)
Frag-dtyType [] fi-[] = f-typ
Frag-dtyType (q ∷ qs) fi = f-pi f-typ (Frag-dtyType qs fi)
Frag-dtyType [] (fi-∷ F fi) = f-pi (Frag-closed F) (Frag-dtyType [] fi)

-- A context in the fragment.
FragCtx : ∀ {n} → Ctx n → Set
FragCtx Γ = ∀ x → Frag (typOf Γ x)

Frag-inst₂ : ∀ {n} {t : Tm (ℕ.suc (ℕ.suc n))} {a b} → Frag t → Frag a → Frag b → Frag (inst₂ t a b)
Frag-inst₂ Ft Fa Fb = Frag-inst (Frag-inst Ft (Frag-wk Fb)) Fa
