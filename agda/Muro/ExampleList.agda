------------------------------------------------------------------------
-- List A, length, and length (cons 1 (cons 1 nil)) ≡ 2.
------------------------------------------------------------------------

module Muro.ExampleList where

open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

nilTy : ∀ {V} → PTm V
nilTy = pi affine typ (λ A → app (dty 0) (var A))

consTy : ∀ {V} → PTm V
consTy =
  pi affine typ (λ A →
  pi affine (var A) (λ _ →
  pi affine (app (dty 0) (var A)) (λ _ →
    app (dty 0) (var A))))

lengthTy : ∀ {V} → PTm V
lengthTy = pi erased typ (λ A → pi affine (app (dty 0) (var A)) (λ _ → nat))

lengthTm : ∀ {V} → PTm V
lengthTm =
  lam erased typ (λ A →
  lam affine (app (dty 0) (var A)) (λ xs →
    mData (var xs) (λ _ → nat)
      ( ze ∷
        lam affine (var A) (λ _ →
        lam affine (app (dty 0) (var A)) (λ as →
          su (app (app (def 0) (var A)) (var as)))) ∷
        [] )))

ones2Ty : Tm 0
ones2Ty = app (dty 0) nat

ones2Tm : Tm 0
ones2Tm =
  app (app (ctor 0 1) (su ze)) (app (app (ctor 0 1) (su ze)) (ctor 0 0))

lenOkTy : Tm 0
lenOkTy = idt nat (app (app (def 0) nat) (def 1)) (su (su ze))

lenOkTm : Tm 0
lenOkTm = rfl

data IsOk {A : Set} : Result A → Set where
  is-ok : (x : A) → IsOk (ok x)

out : ∀ {A} {r : Result A} → IsOk r → A
out (is-ok x) = x

nilTy-ok    : IsOk (unembed∀ nilTy)
consTy-ok   : IsOk (unembed∀ consTy)
lengthTy-ok : IsOk (unembed∀ lengthTy)
lengthTm-ok : IsOk (unembed∀ lengthTm)
nilTy-ok    = is-ok _
consTy-ok   = is-ok _
lengthTy-ok = is-ok _
lengthTm-ok = is-ok _

listDecl : DataDecl
listDecl =
  mkData "List" (affine ∷ [])
    ( mkCtor "nil"  (out nilTy-ok)  ∷
      mkCtor "cons" (out consTy-ok) ∷
      [] )

listBook : Sig
listBook =
  mkSig (listDecl ∷ [])
    ( mkDef "length"       run  (out lengthTy-ok) (out lengthTm-ok) ∷
      mkDef "ones2"        run  ones2Ty           ones2Tm           ∷
      mkDef "length-ones2" evid lenOkTy           lenOkTm           ∷
      [] )

length-ones2-checks : checkSig! listBook ≡ ok tt
length-ones2-checks = refl
