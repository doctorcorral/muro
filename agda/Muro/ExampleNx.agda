------------------------------------------------------------------------
-- I64 / Tensor I64 n wrappers. Kernel ≡ on F32 is refused.
------------------------------------------------------------------------

module Muro.ExampleNx where

open import Data.List.Base using (List; []; _∷_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Unembed
open import Muro.Check

addITy : ∀ {V} → PTm V
addITy = pi affine i64 (λ _ → pi affine i64 (λ _ → i64))

addITm : ∀ {V} → PTm V
addITm =
  lam affine i64 (λ x →
  lam affine i64 (λ y →
    addi (var x) (var y)))

addTTy : ∀ {V} → PTm V
addTTy =
  pi erased i64 (λ n →
  pi reuse (tensor i64 (var n)) (λ _ →
    tensor i64 (var n)))

addTTm : ∀ {V} → PTm V
addTTm =
  lam erased i64 (λ n →
  lam reuse (tensor i64 (var n)) (λ t →
    addt (var t) (var t)))

t1Ty : Tm 0
t1Ty = tensor i64 (toi64 (su (su ze)))

t1Tm : Tm 0
t1Tm = packi (toi64 (su ze)) (toi64 (su (su ze)))

doubledTy : Tm 0
doubledTy = tensor i64 (toi64 (su (su ze)))

doubledTm : Tm 0
doubledTm = app (app (def 1) (toi64 (su (su ze)))) (def 2)

data IsOk {A : Set} : Result A → Set where
  is-ok : (x : A) → IsOk (ok x)

out : ∀ {A} {r : Result A} → IsOk r → A
out (is-ok x) = x

addITy-ok : IsOk (unembed∀ addITy)
addITm-ok : IsOk (unembed∀ addITm)
addTTy-ok : IsOk (unembed∀ addTTy)
addTTm-ok : IsOk (unembed∀ addTTm)
addITy-ok = is-ok _
addITm-ok = is-ok _
addTTy-ok = is-ok _
addTTm-ok = is-ok _

nxBook : Sig
nxBook =
  fromDefs
    ( mkDef "addI"    run (out addITy-ok) (out addITm-ok) ∷
      mkDef "addT"    run (out addTTy-ok) (out addTTm-ok) ∷
      mkDef "t1"      run t1Ty             t1Tm             ∷
      mkDef "doubled" run doubledTy        doubledTm        ∷
      [] )

nx-checks : checkSig! nxBook ≡ ok tt
nx-checks = refl

-- {x ≡ y : F32} is not a type.
badFloatTy : ∀ {V} → PTm V
badFloatTy =
  pi affine f32ty (λ x →
  pi affine f32ty (λ y →
    idt f32ty (var x) (var y)))

badFloatTy-ok : IsOk (unembed∀ badFloatTy)
badFloatTy-ok = is-ok _

badFloatEq : Sig
badFloatEq =
  fromDefs (mkDef "bad" spec (out badFloatTy-ok) rfl ∷ [])

data IsFail {A : Set} : Result A → Set where
  is-fail : (e : String) → IsFail (fail e)

float-eq-rejected : IsFail (checkSig! badFloatEq)
float-eq-rejected = is-fail _

-- {x ≡ y : Tensor F32 n} is not a type.
badTenTy : ∀ {V} → PTm V
badTenTy =
  pi affine i64 (λ n →
  pi affine (tensor f32ty (var n)) (λ x →
  pi affine (tensor f32ty (var n)) (λ y →
    idt (tensor f32ty (var n)) (var x) (var y))))

badTenTy-ok : IsOk (unembed∀ badTenTy)
badTenTy-ok = is-ok _

badTenEq : Sig
badTenEq =
  fromDefs (mkDef "badT" spec (out badTenTy-ok) rfl ∷ [])

tensor-f32-eq-rejected : IsFail (checkSig! badTenEq)
tensor-f32-eq-rejected = is-fail _
