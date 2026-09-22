------------------------------------------------------------------------
-- Data declarations as ⊢ and ⊨ read them, up to conversion.
--
--   IsData σ A        A is a Data type: Nat, Unit, Empty, or a declared
--                     data type applied to Data parameters, after ≈
--                     (Check.isData whnf-normalises before it looks).
--   ReuseOk σ q A     a binder (q x : A) is admissible: + needs Data.
--   InstParams σ T ps R
--                     the constructor type T instantiated at the
--                     parameters ps is R (Check.instParams: peel one Π
--                     per parameter, seen through ≈).
--   BrTy σ i j T P acc X
--                     X is the type of the branch for constructor i.j
--                     whose remaining telescope is T, with motive P and
--                     the constructor arguments seen so far acc
--                     (Check.checkBr: one Π per field, then the motive
--                     at the constructor applied to its fields).
--
-- All are closed under renaming and substitution, and InstParams is
-- functional up to ≈. Nothing here mentions typing; Muro.Judgement and
-- Muro.Typing use these as premises.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Data where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; take)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env
open import Muro.Spine
open import Muro.Reduction
open import Muro.Convert

------------------------------------------------------------------------
-- Data types.
------------------------------------------------------------------------

data IsData (σ : Sig) {n} : Tm n → Set
data AllData (σ : Sig) {n} : List (Tm n) → Set

data IsData σ where
  d-nat   : IsData σ nat
  d-unit  : IsData σ unit
  d-empty : IsData σ empty
  d-dty   : ∀ {i d as e}
    → lookupData σ i ≡ ok d → Spine (dty i) as e
    → AllData σ (take (nparams d) as)
    → IsData σ e
  d-conv  : ∀ {A A′} → σ ⊢[ spec ] A ≈ A′ → IsData σ A′ → IsData σ A

data AllData σ where
  ad-[] : AllData σ []
  ad-∷  : ∀ {A as} → IsData σ A → AllData σ as → AllData σ (A ∷ as)

ReuseOk : Sig → Qty → ∀ {n} → Tm n → Set
ReuseOk σ reuse  A = IsData σ A
ReuseOk σ affine A = ⊤
ReuseOk σ erased A = ⊤

IsData-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {A : Tm n} → IsData σ A → IsData σ (ren ρ A)
AllData-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {as : List (Tm n)}
  → AllData σ as → AllData σ (renList ρ as)

IsData-ren ρ d-nat = d-nat
IsData-ren ρ d-unit = d-unit
IsData-ren ρ d-empty = d-empty
IsData-ren ρ (d-dty {d = d} {as} lk sp ad) =
  d-dty lk (Spine-ren ρ sp)
    (subst (AllData _) (renList-take ρ (nparams d) as) (AllData-ren ρ ad))
IsData-ren ρ (d-conv c d) = d-conv (≈-ren ρ c) (IsData-ren ρ d)

AllData-ren ρ ad-[] = ad-[]
AllData-ren ρ (ad-∷ d ad) = ad-∷ (IsData-ren ρ d) (AllData-ren ρ ad)

IsData-sub : ∀ {σ n k} (τ : Fin n → Tm k) {A : Tm n} → IsData σ A → IsData σ (sub τ A)
AllData-sub : ∀ {σ n k} (τ : Fin n → Tm k) {as : List (Tm n)}
  → AllData σ as → AllData σ (subList τ as)

IsData-sub τ d-nat = d-nat
IsData-sub τ d-unit = d-unit
IsData-sub τ d-empty = d-empty
IsData-sub τ (d-dty {d = d} {as} lk sp ad) =
  d-dty lk (Spine-sub τ sp)
    (subst (AllData _) (subList-take τ (nparams d) as) (AllData-sub τ ad))
IsData-sub τ (d-conv c d) = d-conv (≈-sub τ c) (IsData-sub τ d)

AllData-sub τ ad-[] = ad-[]
AllData-sub τ (ad-∷ d ad) = ad-∷ (IsData-sub τ d) (AllData-sub τ ad)

ReuseOk-ren : ∀ {σ n k} (ρ : Fin n → Fin k) q {A : Tm n}
  → ReuseOk σ q A → ReuseOk σ q (ren ρ A)
ReuseOk-ren ρ reuse  h = IsData-ren ρ h
ReuseOk-ren ρ affine _ = tt
ReuseOk-ren ρ erased _ = tt

ReuseOk-sub : ∀ {σ n k} (τ : Fin n → Tm k) q {A : Tm n}
  → ReuseOk σ q A → ReuseOk σ q (sub τ A)
ReuseOk-sub τ reuse  h = IsData-sub τ h
ReuseOk-sub τ affine _ = tt
ReuseOk-sub τ erased _ = tt

ReuseOk-≈ : ∀ {σ n} q {A A′ : Tm n} → σ ⊢[ spec ] A ≈ A′ → ReuseOk σ q A′ → ReuseOk σ q A
ReuseOk-≈ reuse  c h = d-conv c h
ReuseOk-≈ affine _ _ = tt
ReuseOk-≈ erased _ _ = tt

------------------------------------------------------------------------
-- Instantiating the parameters of a constructor type.
------------------------------------------------------------------------

data InstParams (σ : Sig) {n} : Tm n → List (Tm n) → Tm n → Set where
  ip-[] : ∀ {T} → InstParams σ T [] T
  ip-∷  : ∀ {T q A B p ps R}
    → σ ⊢[ spec ] T ≈ pi q A B
    → InstParams σ (inst B p) ps R
    → InstParams σ T (p ∷ ps) R

InstParams-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {T : Tm n} {ps R}
  → InstParams σ T ps R → InstParams σ (ren ρ T) (renList ρ ps) (ren ρ R)
InstParams-ren ρ ip-[] = ip-[]
InstParams-ren ρ (ip-∷ {B = B} {p = p} c ip) =
  ip-∷ (≈-ren ρ c)
    (subst (λ T → InstParams _ T _ _) (ren-inst ρ B p) (InstParams-ren ρ ip))

InstParams-sub : ∀ {σ n k} (τ : Fin n → Tm k) {T : Tm n} {ps R}
  → InstParams σ T ps R → InstParams σ (sub τ T) (subList τ ps) (sub τ R)
InstParams-sub τ ip-[] = ip-[]
InstParams-sub τ (ip-∷ {B = B} {p = p} c ip) =
  ip-∷ (≈-sub τ c)
    (subst (λ T → InstParams _ T _ _) (sub-inst τ B p) (InstParams-sub τ ip))

-- Functional up to ≈, in the type and in the parameters.
InstParams-≈ : ∀ {σ n} {T T′ : Tm n} {ps ps′ R R′}
  → σ ⊢[ spec ] T ≈ T′ → σ ⊢[ spec ] ps ≈L ps′
  → InstParams σ T ps R → InstParams σ T′ ps′ R′ → σ ⊢[ spec ] R ≈ R′
InstParams-≈ c ≈L-[] ip-[] ip-[] = c
InstParams-≈ c (≈L-∷ cp cps) (ip-∷ c₁ ip₁) (ip-∷ c₂ ip₂)
  with ≈-pi-inj (≈-trans (≈-sym c₁) (≈-trans c c₂))
... | refl , _ , cB = InstParams-≈ (≈-inst₂ cB cp) cps ip₁ ip₂

------------------------------------------------------------------------
-- The type of a branch.
------------------------------------------------------------------------

data BrTy (σ : Sig) (i j : ℕ) : ∀ {n} → Tm n → Tm (ℕ.suc n) → List (Tm n) → Tm n → Set where
  bt-pi  : ∀ {n} {T : Tm n} {q A B P acc X}
    → σ ⊢[ spec ] T ≈ pi q A B
    → ReuseOk σ q A
    → BrTy σ i j B (ren (lift suc) P) (renList suc acc ++ (var zero ∷ [])) X
    → BrTy σ i j T P acc (pi q A X)
  bt-end : ∀ {n} {T : Tm n} {P acc ps D}
    → Spine (dty i) ps D
    → σ ⊢[ spec ] T ≈ D
    → BrTy σ i j T P acc (inst P (appsFrom (ctor i j) acc))

BrTy-≈ : ∀ {σ i j n} {T T′ : Tm n} {P acc X}
  → σ ⊢[ spec ] T ≈ T′ → BrTy σ i j T P acc X → BrTy σ i j T′ P acc X
BrTy-≈ c (bt-pi c′ rok bt) = bt-pi (≈-trans (≈-sym c) c′) rok bt
BrTy-≈ c (bt-end sp c′) = bt-end sp (≈-trans (≈-sym c) c′)

-- Commutations used under the field binder.
lift-lift-suc : ∀ {n k} (ρ : Fin n → Fin k) (x : Fin (ℕ.suc n))
  → lift (lift ρ) (lift suc x) ≡ lift suc (lift ρ x)
lift-lift-suc ρ zero = refl
lift-lift-suc ρ (suc x) = refl

ren-lift-suc : ∀ {n k} (ρ : Fin n → Fin k) (P : Tm (ℕ.suc n))
  → ren (lift (lift ρ)) (ren (lift suc) P) ≡ ren (lift suc) (ren (lift ρ) P)
ren-lift-suc ρ P =
  trans (ren-ren (lift (lift ρ)) (lift suc) P)
    (trans (ren-ext (lift-lift-suc ρ) P) (sym (ren-ren (lift suc) (lift ρ) P)))

renList-acc : ∀ {n k} (ρ : Fin n → Fin k) (acc : List (Tm n))
  → renList (lift ρ) (renList suc acc ++ (var zero ∷ []))
    ≡ renList suc (renList ρ acc) ++ (var zero ∷ [])
renList-acc ρ acc =
  trans (renList-++ (lift ρ) (renList suc acc) (var zero ∷ []))
    (cong (_++ (var zero ∷ []))
      (trans (renList-ren (lift ρ) suc acc) (sym (renList-ren suc ρ acc))))

lifts-lift-suc : ∀ {n k} (τ : Fin n → Tm k) (x : Fin (ℕ.suc n))
  → lifts (lifts τ) (lift suc x) ≡ ren (lift suc) (lifts τ x)
lifts-lift-suc τ zero = refl
lifts-lift-suc τ (suc x) =
  trans (ren-ren suc suc (τ x)) (sym (ren-ren (lift suc) suc (τ x)))

sub-lift-suc : ∀ {n k} (τ : Fin n → Tm k) (P : Tm (ℕ.suc n))
  → sub (lifts (lifts τ)) (ren (lift suc) P) ≡ ren (lift suc) (sub (lifts τ) P)
sub-lift-suc τ P =
  trans (sub-ren (lifts (lifts τ)) (lift suc) P)
    (trans (sub-ext (lifts-lift-suc τ) P) (sym (ren-sub (lift suc) (lifts τ) P)))

subList-acc : ∀ {n k} (τ : Fin n → Tm k) (acc : List (Tm n))
  → subList (lifts τ) (renList suc acc ++ (var zero ∷ []))
    ≡ renList suc (subList τ acc) ++ (var zero ∷ [])
subList-acc τ acc =
  trans (subList-++ (lifts τ) (renList suc acc) (var zero ∷ []))
    (cong (_++ (var zero ∷ []))
      (trans (subList-ren (lifts τ) suc acc) (sym (renList-sub suc τ acc))))

subst₂ : ∀ {A B : Set} (F : A → B → Set) {a a′ b b′}
  → a ≡ a′ → b ≡ b′ → F a b → F a′ b′
subst₂ F refl refl x = x

BrTy-ren : ∀ {σ i j n k} (ρ : Fin n → Fin k) {T : Tm n} {P acc X}
  → BrTy σ i j T P acc X
  → BrTy σ i j (ren ρ T) (ren (lift ρ) P) (renList ρ acc) (ren ρ X)
BrTy-ren ρ (bt-pi {q = q} {P = P} {acc = acc} c rok bt) =
  bt-pi (≈-ren ρ c) (ReuseOk-ren ρ q rok)
    (subst₂ (λ P′ acc′ → BrTy _ _ _ _ P′ acc′ _) (ren-lift-suc ρ P) (renList-acc ρ acc)
      (BrTy-ren (lift ρ) bt))
BrTy-ren {i = i} {j = j} ρ (bt-end {P = P} {acc = acc} sp c)
  rewrite ren-inst ρ P (appsFrom (ctor i j) acc) | ren-appsFrom ρ (ctor i j) acc =
  bt-end (Spine-ren ρ sp) (≈-ren ρ c)

BrTy-sub : ∀ {σ i j n k} (τ : Fin n → Tm k) {T : Tm n} {P acc X}
  → BrTy σ i j T P acc X
  → BrTy σ i j (sub τ T) (sub (lifts τ) P) (subList τ acc) (sub τ X)
BrTy-sub τ (bt-pi {q = q} {P = P} {acc = acc} c rok bt) =
  bt-pi (≈-sub τ c) (ReuseOk-sub τ q rok)
    (subst₂ (λ P′ acc′ → BrTy _ _ _ _ P′ acc′ _) (sub-lift-suc τ P) (subList-acc τ acc)
      (BrTy-sub (lifts τ) bt))
BrTy-sub {i = i} {j = j} τ (bt-end {P = P} {acc = acc} sp c)
  rewrite sub-inst τ P (appsFrom (ctor i j) acc) | sub-appsFrom τ (ctor i j) acc =
  bt-end (Spine-sub τ sp) (≈-sub τ c)

-- Instantiating the field binder: the motive and the earlier arguments
-- were weakened past it, the new argument is var zero.
lifts-instσ-suc : ∀ {n} (a : Tm n) (x : Fin (ℕ.suc n))
  → lifts (instσ a) (lift suc x) ≡ var x
lifts-instσ-suc a zero = refl
lifts-instσ-suc a (suc x) = refl

inst-lift-suc : ∀ {n} (P : Tm (ℕ.suc n)) (a : Tm n)
  → sub (lifts (instσ a)) (ren (lift suc) P) ≡ P
inst-lift-suc P a =
  trans (sub-ren (lifts (instσ a)) (lift suc) P)
    (trans (sub-ext (lifts-instσ-suc a) P) (sub-var P))

subList-var : ∀ {n} (ts : List (Tm n)) → subList var ts ≡ ts
subList-var [] = refl
subList-var (t ∷ ts) rewrite sub-var t | subList-var ts = refl

inst-acc : ∀ {n} (acc : List (Tm n)) (a : Tm n)
  → subList (instσ a) (renList suc acc ++ (var zero ∷ [])) ≡ acc ++ (a ∷ [])
inst-acc acc a =
  trans (subList-++ (instσ a) (renList suc acc) (var zero ∷ []))
    (cong (_++ (a ∷ []))
      (trans (subList-ren (instσ a) suc acc) (subList-var acc)))

BrTy-inst : ∀ {σ i j n} {B : Tm (ℕ.suc n)} {P acc X} (a : Tm n)
  → BrTy σ i j B (ren (lift suc) P) (renList suc acc ++ (var zero ∷ [])) X
  → BrTy σ i j (inst B a) P (acc ++ (a ∷ [])) (inst X a)
BrTy-inst {P = P} {acc = acc} a bt =
  subst₂ (λ P′ acc′ → BrTy _ _ _ _ P′ acc′ _) (inst-lift-suc P a) (inst-acc acc a)
    (BrTy-sub (instσ a) bt)
