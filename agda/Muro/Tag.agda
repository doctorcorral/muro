------------------------------------------------------------------------
-- Constructor tags. `tmTag` numbers the constructors of Tm; `Shape k t`
-- says t is built from constructor number k. The checker compares tags
-- before structural comparison (synEq, convN) so that proofs about
-- those functions can case on two terms of equal tag without listing
-- every off-diagonal pair.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Tag where

open import Data.Nat.Base using (ℕ)
open import Muro.Syntax

tmTag : ∀ {n} → Tm n → ℕ
tmTag (var _) = 0
tmTag typ = 1
tmTag (pi _ _ _) = 2
tmTag (lam _ _ _) = 3
tmTag (app _ _) = 4
tmTag nat = 5
tmTag ze = 6
tmTag (su _) = 7
tmTag unit = 8
tmTag one = 9
tmTag empty = 10
tmTag (dty _) = 11
tmTag (ctor _ _) = 12
tmTag (mData _ _ _) = 13
tmTag (mNat _ _ _ _) = 14
tmTag (mEmp _ _) = 15
tmTag (mUnit _ _ _) = 16
tmTag (idt _ _ _) = 17
tmTag rfl = 18
tmTag (rwt _ _ _) = 19
tmTag (def _) = 20
tmTag (ann _ _) = 21
tmTag (prod _ _) = 22
tmTag (pair _ _) = 23
tmTag (fst _) = 24
tmTag (snd _) = 25
tmTag (nu _) = 26
tmTag (unf _ _) = 27
tmTag (ucons _) = 28
tmTag i64 = 29
tmTag f32ty = 30
tmTag (tensor _ _) = 31
tmTag (addi _ _) = 32
tmTag (muli _ _) = 33
tmTag (addt _ _) = 34
tmTag (toi64 _) = 35
tmTag (packi _ _) = 36

data Shape {n} : ℕ → Tm n → Set where
  sh-var : ∀ {a} → Shape 0 (var a)
  sh-typ : Shape 1 typ
  sh-pi : ∀ {a b c} → Shape 2 (pi a b c)
  sh-lam : ∀ {a b c} → Shape 3 (lam a b c)
  sh-app : ∀ {a b} → Shape 4 (app a b)
  sh-nat : Shape 5 nat
  sh-ze : Shape 6 ze
  sh-su : ∀ {a} → Shape 7 (su a)
  sh-unit : Shape 8 unit
  sh-one : Shape 9 one
  sh-empty : Shape 10 empty
  sh-dty : ∀ {a} → Shape 11 (dty a)
  sh-ctor : ∀ {a b} → Shape 12 (ctor a b)
  sh-mData : ∀ {a b c} → Shape 13 (mData a b c)
  sh-mNat : ∀ {a b c d} → Shape 14 (mNat a b c d)
  sh-mEmp : ∀ {a b} → Shape 15 (mEmp a b)
  sh-mUnit : ∀ {a b c} → Shape 16 (mUnit a b c)
  sh-idt : ∀ {a b c} → Shape 17 (idt a b c)
  sh-rfl : Shape 18 rfl
  sh-rwt : ∀ {a b c} → Shape 19 (rwt a b c)
  sh-def : ∀ {a} → Shape 20 (def a)
  sh-ann : ∀ {a b} → Shape 21 (ann a b)
  sh-prod : ∀ {a b} → Shape 22 (prod a b)
  sh-pair : ∀ {a b} → Shape 23 (pair a b)
  sh-fst : ∀ {a} → Shape 24 (fst a)
  sh-snd : ∀ {a} → Shape 25 (snd a)
  sh-nu : ∀ {a} → Shape 26 (nu a)
  sh-unf : ∀ {a b} → Shape 27 (unf a b)
  sh-ucons : ∀ {a} → Shape 28 (ucons a)
  sh-i64 : Shape 29 i64
  sh-f32ty : Shape 30 f32ty
  sh-tensor : ∀ {a b} → Shape 31 (tensor a b)
  sh-addi : ∀ {a b} → Shape 32 (addi a b)
  sh-muli : ∀ {a b} → Shape 33 (muli a b)
  sh-addt : ∀ {a b} → Shape 34 (addt a b)
  sh-toi64 : ∀ {a} → Shape 35 (toi64 a)
  sh-packi : ∀ {a b} → Shape 36 (packi a b)

shape : ∀ {n} (t : Tm n) → Shape (tmTag t) t
shape (var _) = sh-var
shape typ = sh-typ
shape (pi _ _ _) = sh-pi
shape (lam _ _ _) = sh-lam
shape (app _ _) = sh-app
shape nat = sh-nat
shape ze = sh-ze
shape (su _) = sh-su
shape unit = sh-unit
shape one = sh-one
shape empty = sh-empty
shape (dty _) = sh-dty
shape (ctor _ _) = sh-ctor
shape (mData _ _ _) = sh-mData
shape (mNat _ _ _ _) = sh-mNat
shape (mEmp _ _) = sh-mEmp
shape (mUnit _ _ _) = sh-mUnit
shape (idt _ _ _) = sh-idt
shape rfl = sh-rfl
shape (rwt _ _ _) = sh-rwt
shape (def _) = sh-def
shape (ann _ _) = sh-ann
shape (prod _ _) = sh-prod
shape (pair _ _) = sh-pair
shape (fst _) = sh-fst
shape (snd _) = sh-snd
shape (nu _) = sh-nu
shape (unf _ _) = sh-unf
shape (ucons _) = sh-ucons
shape i64 = sh-i64
shape f32ty = sh-f32ty
shape (tensor _ _) = sh-tensor
shape (addi _ _) = sh-addi
shape (muli _ _) = sh-muli
shape (addt _ _) = sh-addt
shape (toi64 _) = sh-toi64
shape (packi _ _) = sh-packi
