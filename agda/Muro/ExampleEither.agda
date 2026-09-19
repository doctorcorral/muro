------------------------------------------------------------------------
-- Either / Dec / evenDec.
-- Dec P = P ⊎ (P → Empty). A decision, not LEM.
------------------------------------------------------------------------

module Muro.ExampleEither where

open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

IsEven′ Dec′ evenDec′ : ∀ {V} → PTm V
IsEven′  = def 0
Dec′     = def 1
evenDec′ = def 2

isEvenTy : ∀ {V} → PTm V
isEvenTy = pi affine nat (λ _ → typ)

isEvenTm : ∀ {V} → PTm V
isEvenTm =
  lam affine nat (λ n →
    mNat (var n) (λ _ → typ)
      unit
      (λ n1 →
        mNat (var n1) (λ _ → typ)
          empty
          (λ p → app IsEven′ (var p))))

decTy : ∀ {V} → PTm V
decTy = pi affine typ (λ _ → typ)

decTm : ∀ {V} → PTm V
decTm =
  lam affine typ (λ P →
    sum (var P) (pi affine (var P) (λ _ → empty)))

evenDecTy : ∀ {V} → PTm V
evenDecTy = pi affine nat (λ n → app Dec′ (app IsEven′ (var n)))

evenDecTm : ∀ {V} → PTm V
evenDecTm =
  lam affine nat (λ n →
    mNat (var n)
      (λ x → app Dec′ (app IsEven′ (var x)))
      (left one)
      (λ n1 →
        mNat (var n1)
          (λ y → app Dec′ (app IsEven′ (su (var y))))
          (right (lam affine (app IsEven′ (su ze)) (λ e →
            mEmp (var e) (λ _ → empty))))
          (λ p →
            mSum (app evenDec′ (var p))
              (λ _ → app Dec′ (app IsEven′ (su (su (var p)))))
              (λ e → left (var e))
              (λ c → right (var c)))))

data IsOk {A : Set} : Result A → Set where
  is-ok : (x : A) → IsOk (ok x)

out : ∀ {A} {r : Result A} → IsOk r → A
out (is-ok x) = x

isEvenTy-ok  : IsOk (unembed∀ isEvenTy)
isEvenTm-ok  : IsOk (unembed∀ isEvenTm)
decTy-ok     : IsOk (unembed∀ decTy)
decTm-ok     : IsOk (unembed∀ decTm)
evenDecTy-ok : IsOk (unembed∀ evenDecTy)
evenDecTm-ok : IsOk (unembed∀ evenDecTm)

isEvenTy-ok  = is-ok _
isEvenTm-ok  = is-ok _
decTy-ok     = is-ok _
decTm-ok     = is-ok _
evenDecTy-ok = is-ok _
evenDecTm-ok = is-ok _

evenDecBook : Sig
evenDecBook =
  mkDef "IsEven"  spec (out isEvenTy-ok)  (out isEvenTm-ok)  ∷
  mkDef "Dec"     spec (out decTy-ok)     (out decTm-ok)     ∷
  mkDef "evenDec" evid (out evenDecTy-ok) (out evenDecTm-ok) ∷
  []

evenDec-checks : checkSig! evenDecBook ≡ ok tt
evenDec-checks = refl
