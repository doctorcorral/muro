------------------------------------------------------------------------
-- MuroTT v1 syntax.
--
-- Two representations, as required:
--   de Bruijn  Tm n     — metatheory / executable check
--   PHOAS      PTm V    — substitution and example construction
--
-- Raw HOAS (Tm → Tm) is not the inductive syntax.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Syntax where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤)


open import Muro.Base

------------------------------------------------------------------------
-- de Bruijn terms. Index n is the number of free variables.
------------------------------------------------------------------------

data Tm (n : ℕ) : Set where
  var   : Fin n → Tm n
  typ   : Tm n                                 -- Type  (a sort; not Type : Type)
  pi    : Qty → Tm n → Tm (suc n) → Tm n       -- Π (q x : A) → B
  lam   : Qty → Tm n → Tm (suc n) → Tm n       -- λ (q x : A) → e
  app   : Tm n → Tm n → Tm n
  nat   : Tm n
  ze    : Tm n
  su    : Tm n → Tm n
  unit  : Tm n
  one   : Tm n
  empty : Tm n
  -- Non-indexed data: D params, constructor D.j, generic match.
  dty   : ℕ → Tm n
  ctor  : (di ci : ℕ) → Tm n
  mData : Tm n → Tm (suc n) → List (Tm n) → Tm n
  -- match with explicit motive
  mNat  : (scrut : Tm n) (mot : Tm (suc n))
          (tz : Tm n) (ts : Tm (suc n)) → Tm n
  mEmp  : (scrut : Tm n) (mot : Tm (suc n)) → Tm n
  mUnit : (scrut : Tm n) (mot : Tm (suc n)) (tu : Tm n) → Tm n
  -- identity {e₁ ≡ e₂ : A}
  idt   : (A e₁ e₂ : Tm n) → Tm n
  rfl   : Tm n
  -- rewrite eq with explicit motive (x.P) and body : P[rhs]
  rwt   : (eq : Tm n) (mot : Tm (suc n)) (body : Tm n) → Tm n
  def   : ℕ → Tm n                             -- global definition
  ann   : Tm n → Tm n → Tm n                   -- {e : A}
  -- products, sufficient for uncons : Stream A → A × Stream A
  prod  : Tm n → Tm n → Tm n
  pair  : Tm n → Tm n → Tm n
  fst   : Tm n → Tm n
  snd   : Tm n → Tm n
  -- ν X. F  (F binds X at var 0). Stream A = ν X. A × X.
  nu    : Tm (suc n) → Tm n
  unf   : Tm n → Tm n → Tm n                   -- unfold seed (λ s → (head, next))
  ucons : Tm n → Tm n
  -- Nx wrappers. Spec formers; computed values are run.
  -- Nat stays Peano. toI64 is the only Nat → I64 map.
  i64    : Tm n
  f32ty  : Tm n
  tensor : Tm n → Tm n → Tm n                  -- Tensor D S
  addi   : Tm n → Tm n → Tm n
  muli   : Tm n → Tm n → Tm n
  addt   : Tm n → Tm n → Tm n
  toi64  : Tm n → Tm n
  packi  : Tm n → Tm n → Tm n                  -- two I64s; shape toi64 (suc (suc 0))

------------------------------------------------------------------------
-- PHOAS terms. Binders are V → PTm V, not Tm → Tm.
------------------------------------------------------------------------

data PTm (V : Set) : Set where
  var   : V → PTm V
  typ   : PTm V
  pi    : Qty → PTm V → (V → PTm V) → PTm V
  lam   : Qty → PTm V → (V → PTm V) → PTm V
  app   : PTm V → PTm V → PTm V
  nat   : PTm V
  ze    : PTm V
  su    : PTm V → PTm V
  unit  : PTm V
  one   : PTm V
  empty : PTm V
  dty   : ℕ → PTm V
  ctor  : (di ci : ℕ) → PTm V
  mData : PTm V → (V → PTm V) → List (PTm V) → PTm V
  mNat  : PTm V → (V → PTm V) → PTm V → (V → PTm V) → PTm V
  mEmp  : PTm V → (V → PTm V) → PTm V
  mUnit : PTm V → (V → PTm V) → PTm V → PTm V
  idt   : PTm V → PTm V → PTm V → PTm V
  rfl   : PTm V
  rwt   : PTm V → (V → PTm V) → PTm V → PTm V
  def   : ℕ → PTm V
  ann   : PTm V → PTm V → PTm V
  prod  : PTm V → PTm V → PTm V
  pair  : PTm V → PTm V → PTm V
  fst   : PTm V → PTm V
  snd   : PTm V → PTm V
  nu    : (V → PTm V) → PTm V
  unf   : PTm V → PTm V → PTm V
  ucons : PTm V → PTm V
  i64    : PTm V
  f32ty  : PTm V
  tensor : PTm V → PTm V → PTm V
  addi   : PTm V → PTm V → PTm V
  muli   : PTm V → PTm V → PTm V
  addt   : PTm V → PTm V → PTm V
  toi64  : PTm V → PTm V
  packi  : PTm V → PTm V → PTm V

------------------------------------------------------------------------
-- Global definition identifiers (closed book).
------------------------------------------------------------------------

plusId    : ℕ
plusId    = 0
isEvenId  : ℕ
isEvenId  = 1
halfId    : ℕ
halfId    = 2
plusSucId : ℕ
plusSucId = 3
halfOkId  : ℕ
halfOkId  = 4

showDef : ℕ → String
showDef 0 = "plus"
showDef 1 = "IsEven"
showDef 2 = "half"
showDef 3 = "plus_suc"
showDef 4 = "half_ok"
showDef n = "def" ++ show n

------------------------------------------------------------------------
-- Pretty-printer (debugging the decision procedure).
------------------------------------------------------------------------

showTm : ∀ {n} → Tm n → String
showTm (var i)      = "v" ++ show (toℕ i)
showTm typ          = "Type"
showTm (pi q A B)   = "Π(" ++ showQty q ++ " : " ++ showTm A ++ ") → " ++ showTm B
showTm (lam q A t)  = "λ(" ++ showQty q ++ " : " ++ showTm A ++ ") → " ++ showTm t
showTm (app f a)    = "(" ++ showTm f ++ " " ++ showTm a ++ ")"
showTm nat          = "Nat"
showTm ze           = "0"
showTm (su t)       = "suc(" ++ showTm t ++ ")"
showTm unit         = "Unit"
showTm one          = "tt"
showTm empty        = "Empty"
showTm (dty i)      = "D" ++ show i
showTm (ctor i j)   = "c" ++ show i ++ "." ++ show j
showTm (mData e P _) =
  "match " ++ showTm e ++ " motive " ++ showTm P
showTm (mNat e P z s) =
  "matchNat " ++ showTm e ++ " motive " ++ showTm P ++
  " | 0 => " ++ showTm z ++ " | suc => " ++ showTm s
showTm (mEmp e P)   = "matchEmpty " ++ showTm e ++ " motive " ++ showTm P
showTm (mUnit e P u) =
  "matchUnit " ++ showTm e ++ " motive " ++ showTm P ++ " | tt => " ++ showTm u
showTm (idt A a b)  = "{" ++ showTm a ++ " ≡ " ++ showTm b ++ " : " ++ showTm A ++ "}"
showTm rfl          = "refl"
showTm (rwt e P t)  = "rewrite " ++ showTm e ++ " motive " ++ showTm P ++ " in " ++ showTm t
showTm (def i)      = showDef i
showTm (ann e A)    = "{" ++ showTm e ++ " : " ++ showTm A ++ "}"
showTm (prod A B)   = "(" ++ showTm A ++ " × " ++ showTm B ++ ")"
showTm (pair a b)   = "(" ++ showTm a ++ ", " ++ showTm b ++ ")"
showTm (fst t)      = "fst(" ++ showTm t ++ ")"
showTm (snd t)      = "snd(" ++ showTm t ++ ")"
showTm (nu F)       = "ν(" ++ showTm F ++ ")"
showTm (unf s f)    = "unfold " ++ showTm s ++ " " ++ showTm f
showTm (ucons s)    = "uncons " ++ showTm s
showTm i64          = "I64"
showTm f32ty        = "F32"
showTm (tensor d s) = "Tensor(" ++ showTm d ++ " " ++ showTm s ++ ")"
showTm (addi x y)   = "addi(" ++ showTm x ++ " " ++ showTm y ++ ")"
showTm (muli x y)   = "muli(" ++ showTm x ++ " " ++ showTm y ++ ")"
showTm (addt t u)   = "addt(" ++ showTm t ++ " " ++ showTm u ++ ")"
showTm (toi64 t)    = "toI64(" ++ showTm t ++ ")"
showTm (packi x y)  = "packI(" ++ showTm x ++ " " ++ showTm y ++ ")"
