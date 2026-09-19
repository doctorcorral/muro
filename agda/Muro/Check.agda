------------------------------------------------------------------------
-- MuroTT bidirectional checker.
--
-- Spec: the inductive Γ ⊢[ m ] e ⇒ A / Γ ⊢[ m ] e ⇐ A.
-- Decide: fuel-based Result, each clause commented with its ⊢ constructor.
--
-- There is no promotion: spec ↛ evid, evid ↛ run, spec ↛ run.
-- Emit visibility (def vs defp) is an Elixir-only flag on run.
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

-- dmode is run or spec. Emit visibility (def vs defp) is an Elixir-only
-- flag on run; it is not part of this spec.
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
-- Recursion state: run and evid structural descent (not spec).
-- `guarded` is the ν dual of `smaller`: a self-call under the tail of
-- an unfold pair is productive.
------------------------------------------------------------------------

record RecSt (n : ℕ) : Set where
  constructor recst
  field
    self    : Maybe ℕ
    smaller : Vec Bool n
    recOk   : Vec Bool n
    nextOk  : Bool
    guarded : Bool

extRec : ∀ {n} → RecSt n → Bool → Bool → RecSt (suc n)
extRec (recst sl sm rok _ g) newSmall newOk =
  recst sl (newSmall ∷ sm) (newOk ∷ rok) false g

-- Erased binders do not consume the next recursive argument.
keepNext : ∀ {n} → RecSt n → RecSt (suc n) → RecSt (suc n)
keepNext old new =
  recst (RecSt.self new) (RecSt.smaller new) (RecSt.recOk new)
        (RecSt.nextOk old) (RecSt.guarded new)

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
combine run  u v = addUses u v
combine evid u v = addUses u v
combine spec _ _ = ok u0s

combineAlt : ∀ {n} → Mode → UseVec n → UseVec n → UseVec n
combineAlt run  u v = maxUses u v
combineAlt evid u v = maxUses u v
combineAlt spec _ _ = u0s

checkBound : Mode → Qty → Use → Result ⊤
checkBound run  erased U1 = fail "erased variable used computationally"
checkBound evid erased U1 = fail "erased variable used computationally"
checkBound run  erased Uω = fail "erased variable used computationally"
checkBound evid erased Uω = fail "erased variable used computationally"
checkBound run  affine Uω = fail "affine variable used as reusable"
checkBound evid affine Uω = fail "affine variable used as reusable"
checkBound _    _      _  = ok tt

allowedDef : Mode → Mode → Bool
allowedDef run  _    = true
allowedDef evid spec = true
allowedDef evid evid = true
allowedDef spec spec = true
allowedDef _    _    = false

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

mutual
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
  whnf (suc k) σ (mSum e P l r) with whnf k σ e
  ... | left a  = whnf k σ (inst l a)
  ... | right b = whnf k σ (inst r b)
  ... | e′      = mSum e′ P l r
  whnf (suc k) σ (mLst e P n c) with whnf k σ e
  ... | nil        = whnf k σ n
  ... | cons a as  = whnf k σ (instCons c a as)
  ... | e′         = mLst e′ P n c
  whnf (suc k) σ (def i) with lookupDef σ i
  ... | ok d    = whnf k σ (closed (Def.dbody d))
  ... | fail _  = def i
  whnf (suc k) σ (ann e _) = whnf k σ e
  whnf (suc k) σ (fst e) with whnf k σ e
  ... | pair a _ = whnf k σ a
  ... | e′       = fst e′
  whnf (suc k) σ (snd e) with whnf k σ e
  ... | pair _ b = whnf k σ b
  ... | e′       = snd e′
  whnf (suc k) σ (ucons e) = uconsWhnf k σ (whnf k σ e)
  whnf (suc _) _ t = t

  uconsWhnf : ∀ {n} → ℕ → Sig → Tm n → Tm n
  uconsWhnf k σ (unf s f) with whnf k σ (app f s)
  ... | pair h t = pair h (unf t f)
  ... | _        = ucons (unf s f)
  uconsWhnf _ _ e = ucons e

{-# TERMINATING #-}
isData : ∀ {n} → ℕ → Sig → Tm n → Bool
isData k σ t with whnf k σ t
... | nat   = true
... | unit  = true
... | empty = true
... | lst A = isData k σ A
... | _     = false

{-# TERMINATING #-}
runTy : ∀ {n} → Tm n → Bool
runTy nat         = true
runTy unit        = true
runTy empty       = true
runTy (pi _ _ B)  = runTy B
runTy (nu F)      = runTy (inst F unit)
runTy (prod A B)  = runTy A ∧ runTy B
runTy (sum A B)   = runTy A ∧ runTy B
runTy (lst _)     = true
runTy _           = false

isRunType : ∀ {n} → ℕ → Sig → Tm n → Bool
isRunType k σ t = runTy (whnf k σ t)

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
synEq (lst A)        (lst A′)       = synEq A A′
synEq nil            nil            = true
synEq (cons a as)    (cons a′ as′)  = synEq a a′ ∧ synEq as as′
synEq (mLst e P n c) (mLst e′ P′ n′ c′) =
  synEq e e′ ∧ synEq P P′ ∧ synEq n n′ ∧ synEq c c′
synEq (sum A B)      (sum A′ B′)    = synEq A A′ ∧ synEq B B′
synEq (left t)       (left t′)      = synEq t t′
synEq (right t)      (right t′)     = synEq t t′
synEq (mSum e P l r) (mSum e′ P′ l′ r′) =
  synEq e e′ ∧ synEq P P′ ∧ synEq l l′ ∧ synEq r r′
synEq (mNat e P z s) (mNat e′ P′ z′ s′) =
  synEq e e′ ∧ synEq P P′ ∧ synEq z z′ ∧ synEq s s′
synEq (mEmp e P)     (mEmp e′ P′)   = synEq e e′ ∧ synEq P P′
synEq (mUnit e P u)  (mUnit e′ P′ u′) = synEq e e′ ∧ synEq P P′ ∧ synEq u u′
synEq (idt A a b)    (idt A′ a′ b′) = synEq A A′ ∧ synEq a a′ ∧ synEq b b′
synEq rfl            rfl            = true
synEq (rwt e P t)    (rwt e′ P′ t′) = synEq e e′ ∧ synEq P P′ ∧ synEq t t′
synEq (def i)        (def j)        = i ≡ᵇ j
synEq (ann e A)      (ann e′ A′)    = synEq e e′ ∧ synEq A A′
synEq (prod A B)     (prod A′ B′)   = synEq A A′ ∧ synEq B B′
synEq (pair a b)     (pair a′ b′)   = synEq a a′ ∧ synEq b b′
synEq (fst t)        (fst t′)       = synEq t t′
synEq (snd t)        (snd t′)       = synEq t t′
synEq (nu F)         (nu F′)        = synEq F F′
synEq (unf s f)      (unf s′ f′)    = synEq s s′ ∧ synEq f f′
synEq (ucons s)      (ucons s′)     = synEq s s′
synEq _              _              = false

ctorHead : ∀ {n} → Tm n → Bool
ctorHead ze        = true
ctorHead (su _)    = true
ctorHead one       = true
ctorHead (left _)  = true
ctorHead (right _) = true
ctorHead nil       = true
ctorHead (cons _ _) = true
ctorHead _         = false

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
  convN k σ (lst A)       (lst A′)      = conv k σ A A′
  convN k σ nil           nil           = ok tt
  convN k σ (cons a as)   (cons a′ as′) = conv k σ a a′ >> conv k σ as as′
  convN k σ (mLst e P n c) (mLst e′ P′ n′ c′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ n n′ >> conv k σ c c′
  convN k σ (sum A B)     (sum A′ B′)   = conv k σ A A′ >> conv k σ B B′
  convN k σ (left t)      (left t′)     = conv k σ t t′
  convN k σ (right t)     (right t′)    = conv k σ t t′
  convN k σ (mSum e P l r) (mSum e′ P′ l′ r′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ l l′ >> conv k σ r r′
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
  convN k σ (prod A B)    (prod A′ B′)  = conv k σ A A′ >> conv k σ B B′
  convN k σ (pair a b)    (pair a′ b′)  = conv k σ a a′ >> conv k σ b b′
  convN k σ (fst t)       (fst t′)      = conv k σ t t′
  convN k σ (snd t)       (snd t′)      = conv k σ t t′
  convN k σ (nu F)        (nu F′)       = conv k σ F F′
  convN k σ (unf s f)     (unf s′ f′)   = conv k σ s s′ >> conv k σ f f′
  convN k σ (ucons s)     (ucons s′)    = conv k σ s s′
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
  ≈-ιfst : ∀ {σ a b} → fst (pair a b) ≈[ σ ] a
  ≈-ιsnd : ∀ {σ a b} → snd (pair a b) ≈[ σ ] b
  ≈-ιuncons : ∀ {σ s f h t} →
              app f s ≈[ σ ] pair h t →
              ucons (unf s f) ≈[ σ ] pair h (unf t f)
  ≈-ιleft  : ∀ {σ a P l r} → mSum (left a) P l r ≈[ σ ] inst l a
  ≈-ιnil   : ∀ {σ P n c} → mLst nil P n c ≈[ σ ] n
  ≈-ιcons  : ∀ {σ a as P n c} → mLst (cons a as) P n c ≈[ σ ] instCons c a as
  ≈-ιright : ∀ {σ b P l r} → mSum (right b) P l r ≈[ σ ] inst r b

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
  type-el   : ∀ {A} → σ , Γ ⊢[ spec ] A ⇒ typ → σ , Γ ⊢ A wf

data _,_⊢[_]_⇒_ σ Γ where
  ⇒-var-run : ∀ {x}
    → (qtyOf Γ x ≡ erased → ⊥)
    → σ , Γ ⊢[ run ] var x ⇒ typOf Γ x

  ⇒-var-evid : ∀ {x}
    → (qtyOf Γ x ≡ erased → ⊥)
    → σ , Γ ⊢[ evid ] var x ⇒ typOf Γ x

  ⇒-var-spec : ∀ {x}
    → σ , Γ ⊢[ spec ] var x ⇒ typOf Γ x

  ⇒-ze : ∀ {m} → σ , Γ ⊢[ m ] ze ⇒ nat
  ⇒-su : ∀ {m t} → σ , Γ ⊢[ m ] t ⇐ nat → σ , Γ ⊢[ m ] su t ⇒ nat
  ⇒-tt : ∀ {m} → σ , Γ ⊢[ m ] one ⇒ unit

  ⇒-nat   : σ , Γ ⊢[ spec ] nat   ⇒ typ
  ⇒-unit  : σ , Γ ⊢[ spec ] unit  ⇒ typ
  ⇒-empty : σ , Γ ⊢[ spec ] empty ⇒ typ

  ⇒-pi : ∀ {q A B}
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢ B wf
    → σ , Γ ⊢[ spec ] pi q A B ⇒ typ

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
    → σ , Γ ⊢[ spec ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-app-reuse : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi reuse A B
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-idt : ∀ {A a b}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ spec ] a ⇐ A
    → σ , Γ ⊢[ spec ] b ⇐ A
    → σ , Γ ⊢[ spec ] idt A a b ⇒ typ

  ⇒-rwt : ∀ {m A l r eq P t}
    → σ , Γ ⊢[ spec ] eq ⇒ idt A l r
    → σ , ext Γ affine A ⊢ P wf
    → σ , Γ ⊢[ m ] t ⇐ inst P r
    → σ , Γ ⊢[ m ] rwt eq P t ⇒ inst P l

  ⇒-lst : ∀ {A}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ spec ] lst A ⇒ typ

  ⇒-cons : ∀ {m A a as}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] as ⇐ lst A
    → σ , Γ ⊢[ m ] cons a as ⇒ lst A

  ⇒-mLst : ∀ {m A e P n c}
    → σ , Γ ⊢[ m ] e ⇐ lst A
    → σ , ext Γ affine (lst A) ⊢ P wf
    → σ , Γ ⊢[ m ] n ⇐ inst P nil
    → σ , ext (ext Γ affine A) affine (lst (wk A)) ⊢[ m ] c ⇐
        sub (λ { zero → cons (var (suc zero)) (var zero)
               ; (suc i) → var (suc (suc i)) }) P
    → σ , Γ ⊢[ m ] mLst e P n c ⇒ inst P e

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

  ⇒-prod : ∀ {A B}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢ B wf
    → σ , Γ ⊢[ spec ] prod A B ⇒ typ

  ⇒-pair : ∀ {m A B a b}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] b ⇐ B
    → σ , Γ ⊢[ m ] pair a b ⇒ prod A B

  ⇒-fst : ∀ {m A B t}
    → σ , Γ ⊢[ m ] t ⇒ prod A B
    → σ , Γ ⊢[ m ] fst t ⇒ A

  ⇒-snd : ∀ {m A B t}
    → σ , Γ ⊢[ m ] t ⇒ prod A B
    → σ , Γ ⊢[ m ] snd t ⇒ B

  ⇒-nu : ∀ {F}
    → σ , ext Γ affine typ ⊢ F wf
    → σ , Γ ⊢[ spec ] nu F ⇒ typ

  ⇒-unf : ∀ {m S A seed f}
    → σ , Γ ⊢[ m ] seed ⇐ S
    → σ , Γ ⊢[ m ] f ⇐ pi affine S (prod (wk A) (wk S))
    → σ , Γ ⊢[ m ] unf seed f ⇒ nu (prod (wk A) (var zero))

  ⇒-ucons : ∀ {m F s}
    → σ , Γ ⊢[ m ] s ⇐ nu F
    → σ , Γ ⊢[ m ] ucons s ⇒ inst F (nu F)

  ⇒-sum : ∀ {A B}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢ B wf
    → σ , Γ ⊢[ spec ] sum A B ⇒ typ

  ⇒-mSum : ∀ {m A B e P l r}
    → σ , Γ ⊢[ m ] e ⇐ sum A B
    → σ , ext Γ affine (sum A B) ⊢ P wf
    → σ , ext Γ affine A ⊢[ m ] l ⇐ sub (λ { zero → left (var zero) ; (suc i) → var (suc i) }) P
    → σ , ext Γ affine B ⊢[ m ] r ⇐ sub (λ { zero → right (var zero) ; (suc i) → var (suc i) }) P
    → σ , Γ ⊢[ m ] mSum e P l r ⇒ inst P e

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

  ⇐-nil : ∀ {m A}
    → σ , Γ ⊢[ m ] nil ⇐ lst A

  ⇐-cons : ∀ {m A a as}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] as ⇐ lst A
    → σ , Γ ⊢[ m ] cons a as ⇐ lst A

  ⇐-left : ∀ {m A B a}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] left a ⇐ sum A B

  ⇐-right : ∀ {m A B b}
    → σ , Γ ⊢[ m ] b ⇐ B
    → σ , Γ ⊢[ m ] right b ⇐ sum A B

  ⇐-pair : ∀ {m A B a b}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] b ⇐ B
    → σ , Γ ⊢[ m ] pair a b ⇐ prod A B

  ⇐-unf : ∀ {m S F seed f}
    → σ , Γ ⊢[ m ] seed ⇐ S
    → σ , Γ ⊢[ m ] f ⇐ pi affine S (wk (inst F S))
    → σ , Γ ⊢[ m ] unf seed f ⇐ nu F

-- Intentionally absent: spec ⇒ evid, evid ⇒ run, spec ⇒ run.

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

viewProd : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n × Tm n)
viewProd k σ t with whnf k σ t
... | prod A B = ok (A , B)
... | t′       = fail ("expected ×, got " ++ showTm t′)

viewNu : ∀ {n} → ℕ → Sig → Tm n → Result (Tm (suc n))
viewNu k σ t with whnf k σ t
... | nu F = ok F
... | t′   = fail ("expected ν, got " ++ showTm t′)

viewSum : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n × Tm n)
viewSum k σ t with whnf k σ t
... | sum A B = ok (A , B)
... | t′      = fail ("expected Either, got " ++ showTm t′)

hasSelf : ∀ {n} → Maybe ℕ → Tm n → Bool
hasSelf (just j) (def i) = i ≡ᵇ j
hasSelf s (app f a)      = hasSelf s f ∨ hasSelf s a
hasSelf s (su t)         = hasSelf s t
hasSelf s (pair a b)     = hasSelf s a ∨ hasSelf s b
hasSelf s (fst t)        = hasSelf s t
hasSelf s (snd t)        = hasSelf s t
hasSelf s (unf u f)      = hasSelf s u ∨ hasSelf s f
hasSelf s (ucons u)      = hasSelf s u
hasSelf s (lam _ A t)    = hasSelf s A ∨ hasSelf s t
hasSelf s (pi _ A B)     = hasSelf s A ∨ hasSelf s B
hasSelf s (prod A B)     = hasSelf s A ∨ hasSelf s B
hasSelf s (nu F)         = hasSelf s F
hasSelf s (sum A B)      = hasSelf s A ∨ hasSelf s B
hasSelf s (left t)       = hasSelf s t
hasSelf s (right t)      = hasSelf s t
hasSelf s (mSum e P l r) = hasSelf s e ∨ hasSelf s P ∨ hasSelf s l ∨ hasSelf s r
hasSelf s (lst A)        = hasSelf s A
hasSelf s (cons a as)    = hasSelf s a ∨ hasSelf s as
hasSelf s (mLst e P n c) = hasSelf s e ∨ hasSelf s P ∨ hasSelf s n ∨ hasSelf s c
hasSelf s (mNat e P z u) = hasSelf s e ∨ hasSelf s P ∨ hasSelf s z ∨ hasSelf s u
hasSelf s (mEmp e P)     = hasSelf s e ∨ hasSelf s P
hasSelf s (mUnit e P u)  = hasSelf s e ∨ hasSelf s P ∨ hasSelf s u
hasSelf s (idt A a b)    = hasSelf s A ∨ hasSelf s a ∨ hasSelf s b
hasSelf s (rwt e P t)    = hasSelf s e ∨ hasSelf s P ∨ hasSelf s t
hasSelf s (ann e A)      = hasSelf s e ∨ hasSelf s A
hasSelf _ _              = false

-- On run/evid, unfold's λ-body must be a pair and the head must not
-- contain a self-call. spec skips the test.
checkUnfold : ∀ {n} → ℕ → Sig → Mode → RecSt n → Tm n → Result ⊤
checkUnfold _ _ spec _ _ = ok tt
checkUnfold k σ _ rs f = go (whnf k σ f)
  where
    go : ∀ {n} → Tm n → Result ⊤
    go (lam _ _ t) = go t
    go (pair h _)  =
      if hasSelf (RecSt.self rs) h
      then fail "unguarded recursive call"
      else ok tt
    go _ = fail "unfold body must be a pair"

checkNu : ∀ {n} → Mode → Tm n → Tm n → Result ⊤
checkNu spec _ _ = ok tt
checkNu _    T t = go T t
  where
    go : ∀ {n} → Tm n → Tm n → Result ⊤
    go (pi _ _ B) (lam _ _ u) = go B u
    go (nu _)     (unf _ _)   = ok tt
    go (nu _)     _           = fail "ν value must be an unfold"
    go _          _           = ok tt

occurs : ∀ {n} → Fin n → Tm n → Bool
occurs x (var y)        = eqFin x y
occurs x (pi _ A B)     = occurs x A ∨ occurs (suc x) B
occurs x (lam _ A t)    = occurs x A ∨ occurs (suc x) t
occurs x (app f a)      = occurs x f ∨ occurs x a
occurs x (su t)         = occurs x t
occurs x (sum A B)      = occurs x A ∨ occurs x B
occurs x (left t)       = occurs x t
occurs x (right t)      = occurs x t
occurs x (mSum e P l r) = occurs x e ∨ occurs (suc x) P ∨ occurs (suc x) l ∨ occurs (suc x) r
occurs x (lst A)        = occurs x A
occurs x (cons a as)    = occurs x a ∨ occurs x as
occurs x (mLst e P n c) = occurs x e ∨ occurs (suc x) P ∨ occurs x n ∨ occurs (suc (suc x)) c
occurs x (mNat e P z s) = occurs x e ∨ occurs (suc x) P ∨ occurs x z ∨ occurs (suc x) s
occurs x (mEmp e P)     = occurs x e ∨ occurs (suc x) P
occurs x (mUnit e P u)  = occurs x e ∨ occurs (suc x) P ∨ occurs x u
occurs x (idt A a b)    = occurs x A ∨ occurs x a ∨ occurs x b
occurs x (rwt e P t)    = occurs x e ∨ occurs (suc x) P ∨ occurs x t
occurs x (ann e A)      = occurs x e ∨ occurs x A
occurs x (prod A B)     = occurs x A ∨ occurs x B
occurs x (pair a b)     = occurs x a ∨ occurs x b
occurs x (fst t)        = occurs x t
occurs x (snd t)        = occurs x t
occurs x (nu F)         = occurs (suc x) F
occurs x (unf s f)      = occurs x s ∨ occurs x f
occurs x (ucons s)      = occurs x s
occurs _ _              = false

-- X is strictly positive: product/sum ok; not in a Π-domain; not under app.
spos : ∀ {n} → Fin n → Tm n → Bool
spos x (var _)     = true
spos x (prod A B)  = spos x A ∧ spos x B
spos x (sum A B)   = spos x A ∧ spos x B
spos x (pi _ A B)  = not (occurs x A) ∧ spos (suc x) B
spos x (nu F)      = not (occurs (suc x) F)
spos x t           = not (occurs x t)

strictPos : ∀ {n} → Tm (suc n) → Bool
strictPos F = spos zero F

motSucσ : ∀ {n} → Fin (suc n) → Tm (suc n)
motSucσ zero    = su (var zero)
motSucσ (suc i) = var (suc i)

motSuc : ∀ {n} → Tm (suc n) → Tm (suc n)
motSuc P = sub motSucσ P

motConsσ : ∀ {n} → Fin (suc n) → Tm (suc (suc n))
motConsσ zero    = cons (var (suc zero)) (var zero)
motConsσ (suc i) = var (suc (suc i))

motCons : ∀ {n} → Tm (suc n) → Tm (suc (suc n))
motCons P = sub motConsσ P

viewLst : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n)
viewLst k σ t with whnf k σ t
... | lst A = ok A
... | t′    = fail ("expected List, got " ++ showTm t′)

motLeftσ : ∀ {n} → Fin (suc n) → Tm (suc n)
motLeftσ zero    = left (var zero)
motLeftσ (suc i) = var (suc i)

motLeft : ∀ {n} → Tm (suc n) → Tm (suc n)
motLeft P = sub motLeftσ P

motRightσ : ∀ {n} → Fin (suc n) → Tm (suc n)
motRightσ zero    = right (var zero)
motRightσ (suc i) = var (suc i)

motRight : ∀ {n} → Tm (suc n) → Tm (suc n)
motRight P = sub motRightσ P

checkRec : ∀ {n} → ℕ → Sig → Mode → RecSt n → Tm n → Result ⊤
checkRec _ _ spec _ _ = ok tt
checkRec {n} k σ m rs t = go (apps t)
  where
    descend : ℕ → ℕ → List (Tm n) → Bool → Result ⊤
    descend _ _ [] seenComp =
      if seenComp then fail "recursive call does not descend on a smaller argument"
      else ok tt
    descend i j (a ∷ as) seenComp =
      lookupDef σ i >>= λ d →
      nthQty (Def.dtype d) j >>= λ q →
      if eqQty q erased
      then descend i (suc j) as seenComp
      else if isSmallerVar rs a
      then ok tt
      else descend i (suc j) as true

    go : Tm n × List (Tm n) → Result ⊤
    go (def i , args) =
      case RecSt.self rs of λ where
        nothing  → ok tt
        (just j) → if i ≡ᵇ j
          then (if RecSt.guarded rs then ok tt else descend i 0 args false)
          else ok tt
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
  ... | A′  = infer′ k σ rs Γ spec A′ >>= λ (T , _) → conv k σ T typ   -- type-el

  {-# TERMINATING #-}
  infer′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Result (Tm n × UseVec n)
  {-# TERMINATING #-}
  check′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)

  -- ⇒-var-run / ⇒-var-evid / ⇒-var-spec
  infer′ k σ rs Γ run (var x) with qtyOf Γ x
  ... | erased = fail "no promotion: erased variable in run mode"
  ... | q      =
    if isRunType k σ (typOf Γ x)
    then ok (typOf Γ x , oneHot x (if eqQty q reuse then Uω else U1))
    else fail ("no promotion: variable has a spec type " ++ showTm (typOf Γ x))
  infer′ k σ rs Γ evid (var x) with qtyOf Γ x
  ... | erased = fail "no promotion: erased variable in evidence mode"
  ... | q      = ok (typOf Γ x , oneHot x (if eqQty q reuse then Uω else U1))
  infer′ k σ rs Γ spec (var x) = ok (typOf Γ x , u0s)

  -- ⇒-ze
  infer′ k σ rs Γ m ze = ok (nat , u0s)

  -- ⇒-su
  infer′ k σ rs Γ m (su t) =
    check k σ rs Γ m t nat >>= λ u → ok (nat , u)

  -- ⇒-tt
  infer′ k σ rs Γ m one = ok (unit , u0s)

  -- ⇒-nat / ⇒-unit / ⇒-empty  (spec only: these are types)
  infer′ k σ rs Γ run  nat   = fail "no promotion: Nat is an erased term"
  infer′ k σ rs Γ evid nat   = fail "no promotion: Nat is an erased term"
  infer′ k σ rs Γ run  unit  = fail "no promotion: Unit is an erased term"
  infer′ k σ rs Γ evid unit  = fail "no promotion: Unit is an erased term"
  infer′ k σ rs Γ run  empty = fail "no promotion: Empty is an erased term"
  infer′ k σ rs Γ evid empty = fail "no promotion: Empty is an erased term"
  infer′ k σ rs Γ run  typ   = fail "no promotion: Type is an erased term"
  infer′ k σ rs Γ evid typ   = fail "no promotion: Type is an erased term"
  infer′ k σ rs Γ spec nat   = ok (typ , u0s)
  infer′ k σ rs Γ spec unit  = ok (typ , u0s)
  infer′ k σ rs Γ spec empty = ok (typ , u0s)
  infer′ k σ rs Γ spec typ   = fail "Type has no type (no Type : Type)"

  -- ⇒-pi
  infer′ k σ rs Γ run  (pi _ _ _) = fail "no promotion: Π is an erased term"
  infer′ k σ rs Γ evid (pi _ _ _) = fail "no promotion: Π is an erased term"
  infer′ k σ rs Γ spec (pi q A B) =
    checkTy k σ rs Γ A >>
    checkTy k σ (extRec rs false false) (ext Γ q A) B >>
    ok (typ , u0s)

  -- ⇒-lam
  infer′ k σ rs Γ m (lam q A t) =
    checkTy k σ rs Γ A >>
    (if eqQty q reuse
     then guard "+ requires a Data type" (isData k σ A)
     else ok tt) >>
    let rs1 = extRec rs false (RecSt.nextOk rs)
        rs′ = if eqQty q erased then keepNext rs rs1 else rs1
    in infer k σ rs′ (ext Γ q A) m t >>= λ (B , uses) →
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
      argMode : Tm n → Mode
      argMode f with proj₁ (apps f)
      ... | def i =
        case lookupDef σ i of λ where
          (ok d) → if eqMode m evid ∧ eqMode (Def.dmode d) evid then spec else m
          (fail _) → m
      ... | _ = m

      inferArg : Qty → Tm n → UseVec n → Result (UseVec n)
      inferArg erased A fu =
        check k σ rs Γ spec a A >>= λ _ →
        (if eqMode m spec then ok u0s else ok fu)
      inferArg affine A fu =
        check k σ rs Γ (argMode f) a A >>= λ au → combine m fu au
      inferArg reuse A fu =
        guard "+ argument is not Data" (isData k σ A) >>
        check k σ rs Γ (argMode f) a A >>= λ au → combine m fu au

  -- ⇒-idt
  infer′ k σ rs Γ run  (idt _ _ _) = fail "no promotion: identity type is an erased term"
  infer′ k σ rs Γ evid (idt _ _ _) = fail "no promotion: identity type is an erased term"
  infer′ k σ rs Γ spec (idt A a b) =
    checkTy k σ rs Γ A >>
    check k σ rs Γ spec a A >>
    check k σ rs Γ spec b A >>
    ok (typ , u0s)

  -- rfl must be checked (⇐-refl)
  infer′ k σ rs Γ m rfl = fail "refl requires an expected identity type"

  -- ⇒-rwt
  infer′ k σ rs Γ m (rwt eq P t) =
    infer k σ rs Γ evid eq >>= λ (et , _) →
    viewId k σ et >>= λ (A , l , r) →
    checkTy k σ (extRec rs false false) (ext Γ affine A) P >>
    check k σ rs Γ m t (inst P r) >>= λ tu →
    ok (inst P l , tu)

  -- ⇒-lst
  infer′ k σ rs Γ run  (lst _) = fail "no promotion: List is an erased term"
  infer′ k σ rs Γ evid (lst _) = fail "no promotion: List is an erased term"
  infer′ k σ rs Γ spec (lst A) =
    checkTy k σ rs Γ A >>
    ok (typ , u0s)

  -- nil is checked (⇐-nil)
  infer′ k σ rs Γ m nil = fail "nil requires an expected List type"

  -- ⇒-cons
  infer′ k σ rs Γ m (cons a as) =
    infer k σ rs Γ m a >>= λ (A , au) →
    check k σ rs Γ m as (lst A) >>= λ asu →
    combine m au asu >>= λ uses →
    ok (lst A , uses)

  -- ⇒-mLst
  infer′ k σ rs Γ m (mLst e P n c) =
    infer k σ rs Γ m e >>= λ (et , eu) →
    viewLst k σ et >>= λ A →
    checkTy k σ (extRec rs false false) (ext Γ affine (lst A)) P >>
    check k σ rs Γ m n (inst P nil) >>= λ nu →
    let ok? = scrutOk rs e
        rsA  = extRec rs false false
        rsAs = extRec rsA ok? ok?
        Γc   = ext (ext Γ affine A) affine (lst (wk A))
    in check k σ rsAs Γc m c (motCons P) >>= λ cu-uses →
    let (uAs , rest1) = headTail cu-uses
        (uA  , rest0) = headTail rest1
    in checkBound m affine uAs >>
       checkBound m affine uA >>
       let bu = combineAlt m nu rest0
       in combine m eu bu >>= λ uses → ok (inst P e , uses)
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

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
    (if allowedDef (Def.dmode d) m
     then ok tt
     else fail ("no promotion: " ++ showMode (Def.dmode d) ++ " definition " ++ Def.dname d ++ " in " ++ showMode m ++ " mode")) >>
    (if eqMode m run ∧ not (isRunType k σ (closed {n} (Def.dtype d)))
     then fail ("no promotion: definition " ++ Def.dname d ++ " has a spec type")
     else ok tt) >>
    ok (closed {n} (Def.dtype d) , u0s)

  -- ⇒-ann
  infer′ k σ rs Γ m (ann e A) =
    checkTy k σ rs Γ A >>
    check k σ rs Γ m e A >>= λ u → ok (A , u)

  -- ⇒-prod
  infer′ k σ rs Γ run  (prod _ _) = fail "no promotion: × is an erased term"
  infer′ k σ rs Γ evid (prod _ _) = fail "no promotion: × is an erased term"
  infer′ k σ rs Γ spec (prod A B) =
    checkTy k σ rs Γ A >>
    checkTy k σ rs Γ B >>
    ok (typ , u0s)

  -- ⇒-nu
  infer′ k σ rs Γ run  (nu _) = fail "no promotion: ν is an erased term"
  infer′ k σ rs Γ evid (nu _) = fail "no promotion: ν is an erased term"
  infer′ k σ rs Γ spec (nu F) =
    checkTy k σ (extRec rs false false) (ext Γ affine typ) F >>
    guard "ν body is not strictly positive" (strictPos F) >>
    ok (typ , u0s)

  -- ⇒-pair
  infer′ k σ rs Γ m (pair a b) =
    infer k σ rs Γ m a >>= λ (A , au) →
    infer k σ rs Γ m b >>= λ (B , bu) →
    combine m au bu >>= λ uses →
    ok (prod A B , uses)

  -- ⇒-fst
  infer′ k σ rs Γ m (fst t) =
    infer k σ rs Γ m t >>= λ (T , u) →
    viewProd k σ T >>= λ (A , _) →
    ok (A , u)

  -- ⇒-snd
  infer′ k σ rs Γ m (snd t) =
    infer k σ rs Γ m t >>= λ (T , u) →
    viewProd k σ T >>= λ (_ , B) →
    ok (B , u)

  -- ⇒-unf
  infer′ k σ rs Γ m (unf seed f) =
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    infer k σ rs Γ m f >>= λ (ft , fu) →
    viewPi k σ ft >>= λ (_ , S′ , Body) →
    conv k σ S′ S >>
    viewProd k σ (inst Body seed) >>= λ (A , S2) →
    conv k σ S2 S >>
    checkUnfold k σ m rs f >>
    combine m seedU fu >>= λ uses →
    ok (nu (prod (wk A) (var zero)) , uses)

  -- ⇒-ucons
  infer′ k σ rs Γ m (ucons s) =
    infer k σ rs Γ m s >>= λ (T , u) →
    viewNu k σ T >>= λ F →
    ok (inst F T , u)

  -- ⇒-sum
  infer′ k σ rs Γ run  (sum _ _) = fail "no promotion: Either is an erased term"
  infer′ k σ rs Γ evid (sum _ _) = fail "no promotion: Either is an erased term"
  infer′ k σ rs Γ spec (sum A B) =
    checkTy k σ rs Γ A >>
    checkTy k σ rs Γ B >>
    ok (typ , u0s)

  -- left / right are checked (⇐-left / ⇐-right)
  infer′ k σ rs Γ m (left _)  = fail "left requires an expected Either type"
  infer′ k σ rs Γ m (right _) = fail "right requires an expected Either type"

  -- ⇒-mSum
  infer′ k σ rs Γ m (mSum e P l r) =
    infer k σ rs Γ m e >>= λ (et , eu) →
    viewSum k σ et >>= λ (A , B) →
    checkTy k σ (extRec rs false false) (ext Γ affine (sum A B)) P >>
    let ok? = scrutOk rs e
        rsL = extRec rs ok? ok?
        rsR = extRec rs ok? ok?
    in check k σ rsL (ext Γ affine A) m l (motLeft P) >>= λ lu-uses →
    check k σ rsR (ext Γ affine B) m r (motRight P) >>= λ ru-uses →
    let (uL , lus) = headTail lu-uses
        (uR , rus) = headTail ru-uses
    in checkBound m affine uL >>
       checkBound m affine uR >>
       let bu = combineAlt m lus rus
       in combine m eu bu >>= λ uses → ok (inst P e , uses)
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  -- ⇐-lam
  check′ k σ rs Γ m (lam q A t) T with viewPi k σ T
  ... | fail _ = infer k σ rs Γ m (lam q A t) >>= λ (B , u) → conv k σ B T >> ok u
  ... | ok (q′ , A′ , B) =
    guard "λ/Π quantity mismatch" (eqQty q q′) >>
    checkTy k σ rs Γ A >>
    conv k σ A A′ >>
    (if eqQty q reuse then guard "+ requires a Data type" (isData k σ A′) else ok tt) >>
    let rs1 = extRec rs false (RecSt.nextOk rs)
        rs′ = if eqQty q erased then keepNext rs rs1 else rs1
    in check k σ rs′ (ext Γ q A′) m t B >>= λ uses →
    let (u₀ , us) = headTail uses
    in checkBound m q u₀ >> ok us
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  -- ⇐-refl
  check′ k σ rs Γ m rfl T =
    viewId k σ T >>= λ (_ , a , b) →
    conv k σ a b >> ok u0s

  -- ⇐-nil
  check′ k σ rs Γ m nil T =
    viewLst k σ T >>= λ _ →
    ok u0s

  -- ⇐-cons
  check′ k σ rs Γ m (cons a as) T =
    viewLst k σ T >>= λ A →
    check k σ rs Γ m a A >>= λ au →
    check k σ rs Γ m as (lst A) >>= λ asu →
    combine m au asu

  -- ⇐-left
  check′ k σ rs Γ m (left a) T =
    viewSum k σ T >>= λ (A , _) →
    check k σ rs Γ m a A

  -- ⇐-right
  check′ k σ rs Γ m (right b) T =
    viewSum k σ T >>= λ (_ , B) →
    check k σ rs Γ m b B

  -- ⇐-pair
  check′ k σ rs Γ m (pair a b) T =
    viewProd k σ T >>= λ (A , B) →
    check k σ rs Γ m a A >>= λ au →
    check k σ rs Γ m b B >>= λ bu →
    combine m au bu

  -- ⇐-unf (λ may be affine or + on Data)
  check′ k σ rs Γ m (unf seed (lam q A t)) T =
    viewNu k σ T >>= λ F →
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    conv k σ A S >>
    check k σ (extRec rs false (RecSt.nextOk rs)) (ext Γ q S) m t (wk (inst F S)) >>= λ uses →
    let (u₀ , us) = headTail uses
    in checkBound m q u₀ >>
       checkUnfold k σ m rs (lam q A t) >>
       combine m seedU us
    where
      headTail : ∀ {n} → UseVec (suc n) → Use × UseVec n
      headTail (u ∷ us) = u , us

  check′ k σ rs Γ m (unf seed f) T =
    viewNu k σ T >>= λ F →
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    check k σ rs Γ m f (pi affine S (wk (inst F S))) >>= λ fu →
    checkUnfold k σ m rs f >>
    combine m seedU fu

  -- ⇐-conv (default)
  check′ k σ rs Γ m e A =
    infer k σ rs Γ m e >>= λ (B , u) → conv k σ B A >> ok u

------------------------------------------------------------------------
-- Check a whole signature. Each def is its own recursion group.
------------------------------------------------------------------------

emptyRec : RecSt 0
emptyRec = recst nothing [] [] false false

defRec : ℕ → RecSt 0
defRec i = recst (just i) [] [] true false

checkDef : ℕ → Sig → ℕ → Result ⊤
checkDef k σ i =
  lookupDef σ i >>= λ d →
  tag (Def.dname d ++ " type") (checkTy k σ emptyRec [] (Def.dtype d)) >>
  tag (Def.dname d ++ " body") (check k σ (defRec i) [] (Def.dmode d) (Def.dbody d) (Def.dtype d)) >>
  tag (Def.dname d ++ " productivity")
      (checkNu (Def.dmode d) (Def.dtype d) (Def.dbody d)) >>
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
