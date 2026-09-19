------------------------------------------------------------------------
-- MuroTT v1 syntax.
--
-- Two representations, as required:
--   de Bruijn  Tm n     — metatheory / executable check
--   PHOAS      PTm V    — substitution and example construction
--
-- Raw HOAS (Tm → Tm) is not the inductive syntax.
------------------------------------------------------------------------

module Muro.Syntax where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
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
  -- List A
  lst   : Tm n → Tm n
  nil   : Tm n
  cons  : Tm n → Tm n → Tm n
  mLst  : (scrut : Tm n) (mot : Tm (suc n))
          (tn : Tm n) (tc : Tm (suc (suc n))) → Tm n
  -- coproduct A ⊎ B (Either)
  sum   : Tm n → Tm n → Tm n
  left  : Tm n → Tm n
  right : Tm n → Tm n
  mSum  : (scrut : Tm n) (mot : Tm (suc n))
          (tl tr : Tm (suc n)) → Tm n
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
  lst   : PTm V → PTm V
  nil   : PTm V
  cons  : PTm V → PTm V → PTm V
  mLst  : PTm V → (V → PTm V) → PTm V → (V → V → PTm V) → PTm V
  sum   : PTm V → PTm V → PTm V
  left  : PTm V → PTm V
  right : PTm V → PTm V
  mSum  : PTm V → (V → PTm V) → (V → PTm V) → (V → PTm V) → PTm V
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
showTm (lst A)      = "List " ++ showTm A
showTm nil          = "nil"
showTm (cons a as)  = "cons(" ++ showTm a ++ ", " ++ showTm as ++ ")"
showTm (mLst e P n c) =
  "matchList " ++ showTm e ++ " motive " ++ showTm P ++
  " | nil => " ++ showTm n ++ " | cons => " ++ showTm c
showTm (sum A B)    = "(" ++ showTm A ++ " ⊎ " ++ showTm B ++ ")"
showTm (left t)     = "left(" ++ showTm t ++ ")"
showTm (right t)    = "right(" ++ showTm t ++ ")"
showTm (mSum e P l r) =
  "matchEither " ++ showTm e ++ " motive " ++ showTm P ++
  " | left => " ++ showTm l ++ " | right => " ++ showTm r
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
