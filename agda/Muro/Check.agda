------------------------------------------------------------------------
-- MuroTT bidirectional checker.
--
-- Spec: the inductive Γ ⊢[ m ] e ⇒ A / Γ ⊢[ m ] e ⇐ A.
-- Decide: fuel-based Result, each clause commented with its ⊢ constructor.
--
-- There is no promotion rule  dead ⇒ live.
------------------------------------------------------------------------

module Muro.Check where

open import Data.Bool.Base
  using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; lookup; map)
open import Function.Base using (case_of_; _$_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst

------------------------------------------------------------------------
-- Signature of closed definitions.
------------------------------------------------------------------------

record Def : Set where
  constructor mkDef
  field
    dname : String
    dmode : Mode
    dtype : Tm 0
    dbody : Tm 0

Sig : Set
Sig = List Def

lookupDef : Sig → ℕ → Result Def
lookupDef []       _       = fail "unknown definition"
lookupDef (d ∷ _)  zero    = ok d
lookupDef (_ ∷ ds) (suc i) = lookupDef ds i

------------------------------------------------------------------------
-- Contexts. Newest binder is index zero; every type is weakened to n.
------------------------------------------------------------------------

record Bind (n : ℕ) : Set where
  constructor bind
  field
    bqty : Qty
    btyp : Tm n

Ctx : ℕ → Set
Ctx n = Vec (Bind n) n

wkBind : ∀ {n} → Bind n → Bind (suc n)
wkBind (bind q A) = bind q (wk A)

ext : ∀ {n} → Ctx n → Qty → Tm n → Ctx (suc n)
ext Γ q A = bind q (wk A) ∷ map wkBind Γ

qtyOf : ∀ {n} → Ctx n → Fin n → Qty
qtyOf Γ x = Bind.bqty (lookup Γ x)

typOf : ∀ {n} → Ctx n → Fin n → Tm n
typOf Γ x = Bind.btyp (lookup Γ x)

------------------------------------------------------------------------
-- Recursion state: live (and dead) structural descent.
------------------------------------------------------------------------

record RecSt (n : ℕ) : Set where
  constructor recst
  field
    self    : Maybe ℕ
    smaller : Vec Bool n
    recOk   : Vec Bool n
    nextOk  : Bool

extRec : ∀ {n} → RecSt n → Bool → Bool → RecSt (suc n)
extRec (recst sl sm rok _) newSmall newOk =
  recst sl (newSmall ∷ sm) (newOk ∷ rok) false

scrutOk : ∀ {n} → RecSt n → Tm n → Bool
scrutOk rs (var x) = lookup (RecSt.recOk rs) x ∨ lookup (RecSt.smaller rs) x
scrutOk _  _       = false

isSmallerVar : ∀ {n} → RecSt n → Tm n → Bool
isSmallerVar rs (var x) = lookup (RecSt.smaller rs) x
isSmallerVar _  _       = false

------------------------------------------------------------------------
-- Usage vectors.
------------------------------------------------------------------------

UseVec : ℕ → Set
UseVec n = Vec Use n

u0s : ∀ {n} → UseVec n
u0s {zero}  = []
u0s {suc n} = U0 ∷ u0s

oneHot : ∀ {n} → Fin n → Use → UseVec n
oneHot {suc _} zero    u = u  ∷ u0s
oneHot {suc _} (suc i) u = U0 ∷ oneHot i u

addUse : Use → Use → Result Use
addUse U0 u  = ok u
addUse u  U0 = ok u
addUse U1 U1 = fail "affine variable used twice"
addUse Uω _  = ok Uω
addUse _  Uω = ok Uω

addUses : ∀ {n} → UseVec n → UseVec n → Result (UseVec n)
addUses []       []       = ok []
addUses (x ∷ xs) (y ∷ ys) = _∷_ <$> addUse x y ⊛ addUses xs ys

maxUse : Use → Use → Use
maxUse Uω _  = Uω
maxUse _  Uω = Uω
maxUse U1 _  = U1
maxUse _  U1 = U1
maxUse U0 U0 = U0

maxUses : ∀ {n} → UseVec n → UseVec n → UseVec n
maxUses []       []       = []
maxUses (x ∷ xs) (y ∷ ys) = maxUse x y ∷ maxUses xs ys

combine : ∀ {n} → Mode → UseVec n → UseVec n → Result (UseVec n)
combine live u v = addUses u v
combine dead _ _ = ok u0s

combineAlt : ∀ {n} → Mode → UseVec n → UseVec n → UseVec n
combineAlt live u v = maxUses u v
combineAlt dead _ _ = u0s

checkBound : Mode → Qty → Use → Result ⊤
checkBound live erased U1 = fail "erased variable used live"
checkBound live erased Uω = fail "erased variable used live"
checkBound live affine Uω = fail "affine variable used as reusable"
checkBound _    _      _  = ok tt

------------------------------------------------------------------------
-- Small helpers.
------------------------------------------------------------------------

eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin {suc _} zero    zero    = true
eqFin {suc _} (suc i) (suc j) = eqFin i j
eqFin {suc _} zero    (suc _) = false
eqFin {suc _} (suc _) zero    = false

apps : ∀ {n} → Tm n → Tm n × List (Tm n)
apps t = go t []
  where
    go : ∀ {n} → Tm n → List (Tm n) → Tm n × List (Tm n)
    go (app f a) acc = go f (a ∷ acc)
    go f         acc = f , acc

nthQty : ∀ {n} → Tm n → ℕ → Result Qty
nthQty (pi q _ _) zero    = ok q
nthQty (pi _ _ B) (suc i) = nthQty B i
nthQty _          _       = fail "recursive-call spine longer than Π telescope"

------------------------------------------------------------------------
-- Weak-head normalisation (β, ι, δ, ann). Fuel is the clock.
------------------------------------------------------------------------

whnf : ∀ {n} → ℕ → Sig → Tm n → Tm n
whnf zero    _ t = t
whnf (suc k) σ (app f a) with whnf k σ f
... | lam _ _ t = whnf k σ (inst t a)
... | f′        = app f′ a
whnf (suc k) σ (mNat e P z s) with whnf k σ e
... | ze   = whnf k σ z
... | su u = whnf k σ (inst s u)
... | e′   = mNat e′ P z s
whnf (suc k) σ (mUnit e P u) with whnf k σ e
... | one = whnf k σ u
... | e′  = mUnit e′ P u
whnf (suc k) σ (mEmp e P) = mEmp (whnf k σ e) P
whnf (suc k) σ (def i) with lookupDef σ i
... | ok d    = whnf k σ (closed (Def.dbody d))
... | fail _  = def i
whnf (suc k) σ (ann e _) = whnf k σ e
whnf (suc _) _ t = t

isData : ∀ {n} → ℕ → Sig → Tm n → Bool
isData k σ t with whnf k σ t
... | nat   = true
... | unit  = true
... | empty = true
... | _     = false

isLiveType : ∀ {n} → ℕ → Sig → Tm n → Bool
isLiveType k σ t = liveTy (whnf k σ t)
  where
    liveTy : ∀ {n} → Tm n → Bool
    liveTy nat        = true
    liveTy unit       = true
    liveTy empty      = true
    liveTy (pi _ _ B) = liveTy B
    liveTy _          = false

------------------------------------------------------------------------
-- Conversion on weak-head normal forms.
-- Syntactic equality is tried first so recursive defs are not unfolded
-- just to compare a call with itself (otherwise plus n m ≁ plus n m loops).
------------------------------------------------------------------------

synEq : ∀ {n} → Tm n → Tm n → Bool
synEq (var i)        (var j)        = eqFin i j
synEq typ            typ            = true
synEq (pi q A B)     (pi q′ A′ B′)  = eqQty q q′ ∧ synEq A A′ ∧ synEq B B′
synEq (lam q A t)    (lam q′ A′ t′) = eqQty q q′ ∧ synEq A A′ ∧ synEq t t′
synEq (app f a)      (app g b)      = synEq f g ∧ synEq a b
synEq nat            nat            = true
synEq ze             ze             = true
synEq (su a)         (su b)         = synEq a b
synEq unit           unit           = true
synEq one            one            = true
synEq empty          empty          = true
synEq (mNat e P z s) (mNat e′ P′ z′ s′) =
  synEq e e′ ∧ synEq P P′ ∧ synEq z z′ ∧ synEq s s′
synEq (mEmp e P)     (mEmp e′ P′)   = synEq e e′ ∧ synEq P P′
synEq (mUnit e P u)  (mUnit e′ P′ u′) = synEq e e′ ∧ synEq P P′ ∧ synEq u u′
synEq (idt A a b)    (idt A′ a′ b′) = synEq A A′ ∧ synEq a a′ ∧ synEq b b′
synEq rfl            rfl            = true
synEq (rwt e P t)    (rwt e′ P′ t′) = synEq e e′ ∧ synEq P P′ ∧ synEq t t′
synEq (def i)        (def j)        = i ≡ᵇ j
synEq (ann e A)      (ann e′ A′)    = synEq e e′ ∧ synEq A A′
synEq _              _              = false

ctorHead : ∀ {n} → Tm n → Bool
ctorHead ze     = true
ctorHead (su _) = true
ctorHead one    = true
ctorHead _      = false

mutual
  {-# TERMINATING #-}
  convArgs : ∀ {n} → ℕ → Sig → List (Tm n) → List (Tm n) → Result ⊤
  convArgs k σ []       []       = ok tt
  convArgs k σ (a ∷ as) (b ∷ bs) = conv k σ a b >> convArgs k σ as bs
  convArgs _ _ _        _        = fail "conv: spine length mismatch"

  {-# TERMINATING #-}
  conv : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  conv zero    _ _ _ = fail "conv: out of fuel"
  conv {n} (suc k) σ u v =
    if synEq u v then ok tt
    else stuckCong u v
    where
      stuckCong : Tm n → Tm n → Result ⊤
      stuckCong u′ v′ with apps u′ | apps v′
      ... | (def i , a ∷ as) | (def j , b ∷ bs) =
        if (i ≡ᵇ j) ∧ not (ctorHead a) ∧ not (ctorHead b)
        then (conv k σ a b >> convArgs k σ as bs)
        else convN k σ (whnf k σ u′) (whnf k σ v′)
      ... | _ | _ = convN k σ (whnf k σ u′) (whnf k σ v′)

  {-# TERMINATING #-}
  convN : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  convN k σ typ           typ           = ok tt
  convN k σ nat           nat           = ok tt
  convN k σ unit          unit          = ok tt
  convN k σ empty         empty         = ok tt
  convN k σ ze            ze            = ok tt
  convN k σ one           one           = ok tt
  convN k σ rfl           rfl           = ok tt
  convN k σ (su a)        (su b)        = conv k σ a b
  convN k σ (var i)       (var j)       = guard ("var " ++ showTm (var i) ++ " ≠ " ++ showTm (var j)) (eqFin i j)
  convN k σ (def i)       (def j)       = guard ("def " ++ showDef i ++ " ≠ " ++ showDef j) (i ≡ᵇ j)
  convN k σ (pi q A B)    (pi q′ A′ B′) =
    guard "Π quantity mismatch" (eqQty q q′) >> conv k σ A A′ >> conv k σ B B′
  convN k σ (lam q A t)   (lam q′ A′ t′) =
    guard "λ quantity mismatch" (eqQty q q′) >> conv k σ A A′ >> conv k σ t t′
  convN k σ (app f a)     (app g b)     = conv k σ f g >> conv k σ a b
  convN k σ (idt A a b)   (idt A′ a′ b′) = conv k σ A A′ >> conv k σ a a′ >> conv k σ b b′
  convN k σ (mNat e P z s) (mNat e′ P′ z′ s′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ z z′ >> conv k σ s s′
  convN k σ (mEmp e P)    (mEmp e′ P′)  = conv k σ e e′ >> conv k σ P P′
  convN k σ (mUnit e P u) (mUnit e′ P′ u′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ u u′
  convN k σ (rwt e P t)   (rwt e′ P′ t′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ t t′
  convN k σ (ann e A)     (ann e′ A′)   = conv k σ e e′ >> conv k σ A A′
  convN _ _ u             v             =
    fail ("cannot convert " ++ showTm u ++ " ≁ " ++ showTm v)

------------------------------------------------------------------------
-- Spec: conversion as an inductive relation (source of truth for ≡).
------------------------------------------------------------------------

data _≈[_]_ {n} : Tm n → Sig → Tm n → Set where
  ≈-refl  : ∀ {σ t} → t ≈[ σ ] t
  ≈-sym   : ∀ {σ u v} → u ≈[ σ ] v → v ≈[ σ ] u
  ≈-trans : ∀ {σ u v w} → u ≈[ σ ] v → v ≈[ σ ] w → u ≈[ σ ] w
  ≈-β     : ∀ {σ q A t u} → app (lam q A t) u ≈[ σ ] inst t u
  ≈-ιz    : ∀ {σ P z s} → mNat ze P z s ≈[ σ ] z
  ≈-ιs    : ∀ {σ u P z s} → mNat (su u) P z s ≈[ σ ] inst s u
  ≈-ιtt   : ∀ {σ P u} → mUnit one P u ≈[ σ ] u
  ≈-δ     : ∀ {σ i d} → lookupDef σ i ≡ ok d → def i ≈[ σ ] closed (Def.dbody d)
  ≈-ann   : ∀ {σ e A} → ann e A ≈[ σ ] e
  ≈-cong-app : ∀ {σ f f′ a a′} → f ≈[ σ ] f′ → a ≈[ σ ] a′ → app f a ≈[ σ ] app f′ a′
  ≈-cong-su  : ∀ {σ a a′} → a ≈[ σ ] a′ → su a ≈[ σ ] su a′
  ≈-cong-pi  : ∀ {σ q A A′ B B′} → A ≈[ σ ] A′ → B ≈[ σ ] B′ → pi q A B ≈[ σ ] pi q A′ B′
  ≈-cong-idt : ∀ {σ A A′ a a′ b b′} → A ≈[ σ ] A′ → a ≈[ σ ] a′ → b ≈[ σ ] b′ →
               idt A a b ≈[ σ ] idt A′ a′ b′

------------------------------------------------------------------------
-- Spec: bidirectional judgments.
-- Elixir Muro.Check clauses are commented with these constructor names.
------------------------------------------------------------------------

infix 3 _,_⊢[_]_⇒_ _,_⊢[_]_⇐_ _,_⊢_wf

data _,_⊢[_]_⇒_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊢[_]_⇐_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊢_wf    (σ : Sig) {n} (Γ : Ctx n) : Tm n → Set

data _,_⊢_wf σ Γ where
  type-Type : σ , Γ ⊢ typ wf                          -- Type is a sort, not Type : Type
  type-el   : ∀ {A} → σ , Γ ⊢[ dead ] A ⇒ typ → σ , Γ ⊢ A wf

data _,_⊢[_]_⇒_ σ Γ where
  ⇒-var-live : ∀ {x}
    → (qtyOf Γ x ≡ erased → ⊥)
    → σ , Γ ⊢[ live ] var x ⇒ typOf Γ x

  ⇒-var-dead : ∀ {x}
    → σ , Γ ⊢[ dead ] var x ⇒ typOf Γ x

  ⇒-ze : ∀ {m} → σ , Γ ⊢[ m ] ze ⇒ nat
  ⇒-su : ∀ {m t} → σ , Γ ⊢[ m ] t ⇐ nat → σ , Γ ⊢[ m ] su t ⇒ nat
  ⇒-tt : ∀ {m} → σ , Γ ⊢[ m ] one ⇒ unit

  ⇒-nat   : σ , Γ ⊢[ dead ] nat   ⇒ typ
  ⇒-unit  : σ , Γ ⊢[ dead ] unit  ⇒ typ
  ⇒-empty : σ , Γ ⊢[ dead ] empty ⇒ typ

  ⇒-pi : ∀ {q A B}
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢ B wf
    → σ , Γ ⊢[ dead ] pi q A B ⇒ typ

  ⇒-lam : ∀ {m q A t B}
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢[ m ] t ⇒ B
    → σ , Γ ⊢[ m ] lam q A t ⇒ pi q A B

  ⇒-app-aff : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi affine A B
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-app-era : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi erased A B
    → σ , Γ ⊢[ dead ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-app-reuse : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi reuse A B
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-idt : ∀ {A a b}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ dead ] a ⇐ A
    → σ , Γ ⊢[ dead ] b ⇐ A
    → σ , Γ ⊢[ dead ] idt A a b ⇒ typ

  ⇒-rwt : ∀ {m A l r eq P t}
    → σ , Γ ⊢[ dead ] eq ⇒ idt A l r
    → σ , ext Γ affine A ⊢ P wf
    → σ , Γ ⊢[ m ] t ⇐ inst P r
    → σ , Γ ⊢[ m ] rwt eq P t ⇒ inst P l

  ⇒-mNat : ∀ {m e P z s}
    → σ , Γ ⊢[ m ] e ⇐ nat
    → σ , ext Γ affine nat ⊢ P wf
    → σ , Γ ⊢[ m ] z ⇐ inst P ze
    → σ , ext Γ affine nat ⊢[ m ] s ⇐ sub (λ { zero → su (var zero) ; (suc i) → var (suc i) }) P
    → σ , Γ ⊢[ m ] mNat e P z s ⇒ inst P e

  ⇒-mEmp : ∀ {m e P}
    → σ , Γ ⊢[ m ] e ⇐ empty
    → σ , ext Γ affine empty ⊢ P wf
    → σ , Γ ⊢[ m ] mEmp e P ⇒ inst P e

  ⇒-mUnit : ∀ {m e P u}
    → σ , Γ ⊢[ m ] e ⇐ unit
    → σ , ext Γ affine unit ⊢ P wf
    → σ , Γ ⊢[ m ] u ⇐ inst P one
    → σ , Γ ⊢[ m ] mUnit e P u ⇒ inst P e

  ⇒-def : ∀ {m i d}
    → lookupDef σ i ≡ ok d
    → σ , Γ ⊢[ m ] def i ⇒ closed (Def.dtype d)

  ⇒-ann : ∀ {m e A}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ m ] e ⇐ A
    → σ , Γ ⊢[ m ] ann e A ⇒ A

data _,_⊢[_]_⇐_ σ Γ where
  ⇐-conv : ∀ {m e A B}
    → σ , Γ ⊢[ m ] e ⇒ B
    → B ≈[ σ ] A
    → σ , Γ ⊢[ m ] e ⇐ A

  ⇐-lam : ∀ {m q A A′ t B}
    → σ , Γ ⊢ A wf
    → A ≈[ σ ] A′
    → σ , ext Γ q A′ ⊢[ m ] t ⇐ B
    → σ , Γ ⊢[ m ] lam q A t ⇐ pi q A′ B

  ⇐-refl : ∀ {m A a b}
    → a ≈[ σ ] b
    → σ , Γ ⊢[ m ] rfl ⇐ idt A a b

-- Intentionally absent:  Γ ⊢[ dead ] e : A  implies  Γ ⊢[ live ] e : A.

------------------------------------------------------------------------
-- Decision procedure.
------------------------------------------------------------------------

viewPi : ∀ {n} → ℕ → Sig → Tm n → Result (Qty × Tm n × Tm (suc n))
viewPi k σ t with whnf k σ t
... | pi q A B = ok (q , A , B)
... | t′       = fail ("expected Π, got " ++ showTm t′)

viewId : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n × Tm n × Tm n)
viewId k σ t with whnf k σ t
... | idt A a b = ok (A , a , b)
... | t′        = fail ("expected Id, got " ++ showTm t′)

motSucσ : ∀ {n} → Fin (suc n) → Tm (suc n)
motSucσ zero    = su (var zero)
motSucσ (suc i) = var (suc i)

motSuc : ∀ {n} → Tm (suc n) → Tm (suc n)
motSuc P = sub motSucσ P

checkRec : ∀ {n} → ℕ → Sig → Mode → RecSt n → Tm n → Result ⊤
checkRec {n} k σ m rs t = go (apps t)
  where
    descend : ℕ → ℕ → List (Tm n) → Result ⊤
    descend _ _ [] = fail "recursive call does not descend on a smaller argument"
    descend i j (a ∷ as) =
      if isSmallerVar rs a
      then (if eqMode m live
            then (lookupDef σ i >>= λ d →
                  nthQty (Def.dtype d) j >>= λ q →
                  if eqQty q erased
                  then descend i (suc j) as
                  else ok tt)
            else ok tt)
      else descend i (suc j) as

    go : Tm n × List (Tm n) → Result ⊤
    go (def i , args) =
      case RecSt.self rs of λ where
        nothing  → ok tt
        (just j) → if i ≡ᵇ j then descend i 0 args else ok tt
    go _ = ok tt

mutual
  {-# TERMINATING #-}
  infer : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Result (Tm n × UseVec n)
  infer k σ rs Γ m t = infer′ k σ rs Γ m t

  {-# TERMINATING #-}
  check : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)
  check k σ rs Γ m e A = check′ k σ rs Γ m e A

  {-# TERMINATING #-}
  checkTy : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Tm n → Result ⊤
  checkTy k σ rs Γ A with whnf k σ A
  ... | typ = ok tt                                          -- type-Type
  ... | A′  = infer′ k σ rs Γ dead A′ >>= λ (T , _) → conv k σ T typ   -- type-el

  {-# TERMINATING #-}
  infer′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Result (Tm n × UseVec n)
  {-# TERMINATING #-}
  check′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)

  -- ⇒-var-live / ⇒-var-dead
  infer′ k σ rs Γ live (var x) with qtyOf Γ x
  ... | erased = fail "no promotion: erased variable in live mode"
  ... | q      =
    if isLiveType k σ (typOf Γ x)
    then ok (typOf Γ x , oneHot x (if eqQty q reuse then Uω else U1))
    else fail ("no promotion: variable has dead type " ++ showTm (typOf Γ x))
  infer′ k σ rs Γ dead (var x) = ok (typOf Γ x , u0s)

  -- ⇒-ze
  infer′ k σ rs Γ m ze = ok (nat , u0s)

  -- ⇒-su
  infer′ k σ rs Γ m (su t) =
    check k σ rs Γ m t nat >>= λ u → ok (nat , u)

  -- ⇒-tt
  infer′ k σ rs Γ m one = ok (unit , u0s)

  -- ⇒-nat / ⇒-unit / ⇒-empty  (dead only: these are types)
  infer′ k σ rs Γ live nat   = fail "no promotion: Nat is dead"
  infer′ k σ rs Γ live unit  = fail "no promotion: Unit is dead"
  infer′ k σ rs Γ live empty = fail "no promotion: Empty is dead"
  infer′ k σ rs Γ live typ   = fail "no promotion: Type is dead"
  infer′ k σ rs Γ dead nat   = ok (typ , u0s)
  infer′ k σ rs Γ dead unit  = ok (typ , u0s)
  infer′ k σ rs Γ dead empty = ok (typ , u0s)
  infer′ k σ rs Γ dead typ   = fail "Type has no type (no Type : Type)"

  -- ⇒-pi
  infer′ k σ rs Γ live (pi _ _ _) = fail "no promotion: Π is dead"
  infer′ k σ rs Γ dead (pi q A B) =
    checkTy k σ rs Γ A >>
    checkTy k σ (extRec rs false false) (ext Γ q A) B >>
    ok (typ , u0s)

  -- ⇒-lam
  infer′ k σ rs Γ m (lam q A t) =
    checkTy k σ rs Γ A >>
    (if eqQty q reuse
     then guard "+ requires a Data type" (isData k σ A)
     else ok tt) >>
    infer k σ (extRec rs false (RecSt.nextOk rs)) (ext Γ q A) m t >>= λ (B , uses) →
    let (u₀ , us) = headTail uses
    in checkBound m q u₀ >> ok (pi q A B , us)
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  -- ⇒-app-aff / ⇒-app-era / ⇒-app-reuse
  infer′ {n} k σ rs Γ m (app f a) =
    infer k σ rs Γ m f >>= λ (ft , fu) →
    viewPi k σ ft >>= λ (q , A , B) →
    inferArg q A fu >>= λ uses →
    checkRec k σ m rs (app f a) >>
    ok (inst B a , uses)
    where
      inferArg : Qty → Tm n → UseVec n → Result (UseVec n)
      inferArg erased A fu =
        check k σ rs Γ dead a A >>= λ _ →
        (if eqMode m live then ok fu else ok u0s)
      inferArg affine A fu =
        check k σ rs Γ m a A >>= λ au → combine m fu au
      inferArg reuse A fu =
        guard "+ argument is not Data" (isData k σ A) >>
        check k σ rs Γ m a A >>= λ au → combine m fu au

  -- ⇒-idt
  infer′ k σ rs Γ live (idt _ _ _) = fail "no promotion: identity type is dead"
  infer′ k σ rs Γ dead (idt A a b) =
    checkTy k σ rs Γ A >>
    check k σ rs Γ dead a A >>
    check k σ rs Γ dead b A >>
    ok (typ , u0s)

  -- rfl must be checked (⇐-refl)
  infer′ k σ rs Γ m rfl = fail "refl requires an expected identity type"

  -- ⇒-rwt
  infer′ k σ rs Γ m (rwt eq P t) =
    infer k σ rs Γ dead eq >>= λ (et , _) →
    viewId k σ et >>= λ (A , l , r) →
    checkTy k σ (extRec rs false false) (ext Γ affine A) P >>
    check k σ rs Γ m t (inst P r) >>= λ tu →
    ok (inst P l , tu)

  -- ⇒-mNat
  infer′ k σ rs Γ m (mNat e P z s) =
    check k σ rs Γ m e nat >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine nat) P >>
    check k σ rs Γ m z (inst P ze) >>= λ zu →
    let ok? = scrutOk rs e
        rs′ = extRec rs ok? ok?
        Γ′  = ext Γ affine nat
    in check k σ rs′ Γ′ m s (motSuc P) >>= λ su-uses →
    let (u₀ , sus) = headTail su-uses
    in checkBound m affine u₀ >>
       let bu = combineAlt m zu sus
       in combine m eu bu >>= λ uses → ok (inst P e , uses)
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  -- ⇒-mEmp
  infer′ k σ rs Γ m (mEmp e P) =
    check k σ rs Γ m e empty >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine empty) P >>
    ok (inst P e , eu)

  -- ⇒-mUnit
  infer′ k σ rs Γ m (mUnit e P u) =
    check k σ rs Γ m e unit >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine unit) P >>
    check k σ rs Γ m u (inst P one) >>= λ uu →
    combine m eu uu >>= λ uses → ok (inst P e , uses)

  -- ⇒-def
  infer′ {n} k σ rs Γ m (def i) =
    lookupDef σ i >>= λ d →
    (if eqMode m live ∧ eqMode (Def.dmode d) dead
     then fail ("no promotion: dead definition " ++ Def.dname d ++ " in live mode")
     else ok tt) >>
    (if eqMode m live ∧ not (isLiveType k σ (closed {n} (Def.dtype d)))
     then fail ("no promotion: definition " ++ Def.dname d ++ " has a dead type")
     else ok tt) >>
    ok (closed {n} (Def.dtype d) , u0s)

  -- ⇒-ann
  infer′ k σ rs Γ m (ann e A) =
    checkTy k σ rs Γ A >>
    check k σ rs Γ m e A >>= λ u → ok (A , u)

  -- ⇐-lam
  check′ k σ rs Γ m (lam q A t) T with viewPi k σ T
  ... | fail _ = infer k σ rs Γ m (lam q A t) >>= λ (B , u) → conv k σ B T >> ok u
  ... | ok (q′ , A′ , B) =
    guard "λ/Π quantity mismatch" (eqQty q q′) >>
    checkTy k σ rs Γ A >>
    conv k σ A A′ >>
    (if eqQty q reuse then guard "+ requires a Data type" (isData k σ A′) else ok tt) >>
    check k σ (extRec rs false (RecSt.nextOk rs)) (ext Γ q A′) m t B >>= λ uses →
    let (u₀ , us) = headTail uses
    in checkBound m q u₀ >> ok us
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  -- ⇐-refl
  check′ k σ rs Γ m rfl T =
    viewId k σ T >>= λ (_ , a , b) →
    conv k σ a b >> ok u0s

  -- ⇐-conv (default)
  check′ k σ rs Γ m e A =
    infer k σ rs Γ m e >>= λ (B , u) → conv k σ B A >> ok u

------------------------------------------------------------------------
-- Check a whole signature. Each def is its own recursion group.
------------------------------------------------------------------------

emptyRec : RecSt 0
emptyRec = recst nothing [] [] false

defRec : ℕ → RecSt 0
defRec i = recst (just i) [] [] true

checkDef : ℕ → Sig → ℕ → Result ⊤
checkDef k σ i =
  lookupDef σ i >>= λ d →
  tag (Def.dname d ++ " type") (checkTy k σ emptyRec [] (Def.dtype d)) >>
  tag (Def.dname d ++ " body") (check k σ (defRec i) [] (Def.dmode d) (Def.dbody d) (Def.dtype d)) >>
  ok tt

checkSig : ℕ → Sig → Result ⊤
checkSig k σ = go 0 σ
  where
    go : ℕ → List Def → Result ⊤
    go _ []       = ok tt
    go i (_ ∷ ds) = checkDef k σ i >> go (suc i) ds

-- Default fuel for closed examples.
fuel : ℕ
fuel = 2000

checkSig! : Sig → Result ⊤
checkSig! = checkSig fuel
