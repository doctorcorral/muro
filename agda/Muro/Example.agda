------------------------------------------------------------------------
-- The v1 example: IsEven, half, plus, plus_suc, half_ok.
--
--   IsEven : Nat → Type
--   half   : Nat → Nat
--   half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
--
-- Proofs are ordinary terms: match + refl + rewrite with motive.
------------------------------------------------------------------------

module Muro.Example where

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Unembed
open import Muro.Check

------------------------------------------------------------------------
-- PHOAS constructors for the book.
------------------------------------------------------------------------

Plus IsEven half plusSuc halfOk : ∀ {V} → PTm V
Plus    = def plusId
IsEven  = def isEvenId
half    = def halfId
plusSuc = def plusSucId
halfOk  = def halfOkId

_·_ : ∀ {V} → PTm V → PTm V → PTm V
_·_ = app
infixl 10 _·_

plusTy : ∀ {V} → PTm V
plusTy = pi affine nat (λ _ → pi affine nat (λ _ → nat))

plusTm : ∀ {V} → PTm V
plusTm =
  lam affine nat (λ n →
  lam affine nat (λ m →
    mNat (var n) (λ _ → nat)
      (var m)
      (λ n′ → su ((Plus · var n′) · var m))))

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
          (λ p → IsEven · var p)))

halfTy : ∀ {V} → PTm V
halfTy = pi affine nat (λ _ → nat)

halfTm : ∀ {V} → PTm V
halfTm =
  lam affine nat (λ n →
    mNat (var n) (λ _ → nat)
      ze
      (λ n1 →
        mNat (var n1) (λ _ → nat)
          ze
          (λ p → su (half · var p))))

plusSucTy : ∀ {V} → PTm V
plusSucTy =
  pi affine nat (λ n →
  pi affine nat (λ m →
    idt nat ((Plus · var n) · su (var m))
            (su ((Plus · var n) · var m))))

plusSucTm : ∀ {V} → PTm V
plusSucTm =
  lam affine nat (λ n →
  lam affine nat (λ m →
    mNat (var n)
      (λ n′ →
        idt nat ((Plus · var n′) · su (var m))
                (su ((Plus · var n′) · var m)))
      rfl
      (λ n′ →
        rwt ((plusSuc · var n′) · var m)
            (λ z → idt nat (su (var z))
                           (su (su ((Plus · var n′) · var m))))
            rfl)))

-- half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
halfOkTy : ∀ {V} → PTm V
halfOkTy =
  pi affine nat (λ n →
  pi affine (IsEven · var n) (λ _ →
    idt nat ((Plus · (half · var n)) · (half · var n))
            (var n)))

idHalf : ∀ {V} → PTm V → PTm V
idHalf x = idt nat ((Plus · (half · x)) · (half · x)) x

halfOkTm : ∀ {V} → PTm V
halfOkTm =
  lam affine nat (λ n →
  lam affine (IsEven · var n) (λ e →
    app (evenMatch n) (var e)))
  where
    evenStep : ∀ {W} → W → PTm W
    evenStep p =
      lam affine (IsEven · su (su (var p))) (λ e2 →
        rwt ((plusSuc · (half · var p)) · (half · var p))
            (λ z → idt nat (su (var z)) (su (su (var p))))
            (rwt ((halfOk · var p) · var e2)
                 (λ z → idt nat (su (su (var z))) (su (su (var p))))
                 rfl))

    oddMatch : ∀ {W} → W → PTm W
    oddMatch n1 =
      mNat (var n1)
        (λ y → pi affine (IsEven · su (var y)) (λ _ → idHalf (su (var y))))
        (lam affine (IsEven · su ze) (λ e1 →
          mEmp (var e1) (λ _ → idHalf (su ze))))
        (λ p → evenStep p)

    evenMatch : ∀ {W} → W → PTm W
    evenMatch n =
      mNat (var n)
        (λ x → pi affine (IsEven · var x) (λ _ → idHalf (var x)))
        (lam affine (IsEven · ze) (λ _ → rfl))
        (λ n1 → oddMatch n1)

------------------------------------------------------------------------
-- Unembed PHOAS → de Bruijn. IsOk forces the conversion to succeed.
------------------------------------------------------------------------

data IsOk {A : Set} : Result A → Set where
  is-ok : (x : A) → IsOk (ok x)

out : ∀ {A} {r : Result A} → IsOk r → A
out (is-ok x) = x

plusTy-ok    : IsOk (unembed∀ plusTy)
plusTm-ok    : IsOk (unembed∀ plusTm)
isEvenTy-ok  : IsOk (unembed∀ isEvenTy)
isEvenTm-ok  : IsOk (unembed∀ isEvenTm)
halfTy-ok    : IsOk (unembed∀ halfTy)
halfTm-ok    : IsOk (unembed∀ halfTm)
plusSucTy-ok : IsOk (unembed∀ plusSucTy)
plusSucTm-ok : IsOk (unembed∀ plusSucTm)
halfOkTy-ok  : IsOk (unembed∀ halfOkTy)
halfOkTm-ok  : IsOk (unembed∀ halfOkTm)

plusTy-ok    = is-ok _
plusTm-ok    = is-ok _
isEvenTy-ok  = is-ok _
isEvenTm-ok  = is-ok _
halfTy-ok    = is-ok _
halfTm-ok    = is-ok _
plusSucTy-ok = is-ok _
plusSucTm-ok = is-ok _
halfOkTy-ok  = is-ok _
halfOkTm-ok  = is-ok _

book : Sig
book = fromDefs (
  mkDef "plus"     run  (out plusTy-ok)    (out plusTm-ok)    ∷
  mkDef "IsEven"   spec (out isEvenTy-ok)  (out isEvenTm-ok)  ∷
  mkDef "half"     run  (out halfTy-ok)    (out halfTm-ok)    ∷
  mkDef "plus_suc" evid (out plusSucTy-ok) (out plusSucTm-ok) ∷
  mkDef "half_ok"  evid (out halfOkTy-ok)  (out halfOkTm-ok)  ∷
  [])

-- Closed computation: plus (half 2) (half 2) ≡ 2.
t2 : Tm 0
t2 = su (su ze)

plus-half-2 : Tm 0
plus-half-2 =
  app (app (def plusId) (app (def halfId) t2))
      (app (def halfId) t2)

plus-half-2-conv : conv fuel book plus-half-2 t2 ≡ ok tt
plus-half-2-conv = refl

half_ok-checks : checkSig! book ≡ ok tt
half_ok-checks = refl
