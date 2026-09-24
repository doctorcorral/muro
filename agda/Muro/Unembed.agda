------------------------------------------------------------------------
-- unembed : PHOAS → de Bruijn.
--
-- Apply each PHOAS binder to a fresh ℕ and read the name stack back as
-- de Bruijn indices. Parametric PHOAS terms do not inspect the ℕ.
-- Agda cannot see termination after applying a binder, so this module
-- is not --safe. The checker does not use it.
------------------------------------------------------------------------

module Muro.Unembed where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)

open import Muro.Base
open import Muro.Syntax

eqNat : ℕ → ℕ → Bool
eqNat zero    zero    = true
eqNat (suc m) (suc n) = eqNat m n
eqNat _       _       = false

findName : ∀ {n} → ℕ → Vec ℕ n → Result (Fin n)
findName x [] = fail "unembed: free name"
findName x (y ∷ ys) with eqNat x y
... | true  = ok zero
... | false = suc <$> findName x ys

mutual
  {-# TERMINATING #-}
  unembedList : ∀ {n} → ℕ → Vec ℕ n → List (PTm ℕ) → Result (List (Tm n))
  unembedList nxt env []       = ok []
  unembedList nxt env (t ∷ ts) = _∷_ <$> unembedN nxt env t ⊛ unembedList nxt env ts

  {-# TERMINATING #-}
  unembedN : ∀ {n} → ℕ → Vec ℕ n → PTm ℕ → Result (Tm n)
  unembedN nxt env (var x)        = var <$> findName x env
  unembedN nxt env typ            = ok typ
  unembedN nxt env (pi q A B)     =
    pi q <$> unembedN nxt env A ⊛ unembedN (suc nxt) (nxt ∷ env) (B nxt)
  unembedN nxt env (lam q A t)    =
    lam q <$> unembedN nxt env A ⊛ unembedN (suc nxt) (nxt ∷ env) (t nxt)
  unembedN nxt env (app f a)      =
    app <$> unembedN nxt env f ⊛ unembedN nxt env a
  unembedN nxt env nat            = ok nat
  unembedN nxt env ze             = ok ze
  unembedN nxt env (su t)         = su <$> unembedN nxt env t
  unembedN nxt env unit           = ok unit
  unembedN nxt env one            = ok one
  unembedN nxt env empty          = ok empty
  unembedN nxt env (dty i)        = ok (dty i)
  unembedN nxt env (ctor i j)     = ok (ctor i j)
  unembedN nxt env (mData e P bs) =
    mData <$> unembedN nxt env e
          ⊛ unembedN (suc nxt) (nxt ∷ env) (P nxt)
          ⊛ unembedList nxt env bs
  unembedN nxt env (mNat e P z s) =
    mNat <$> unembedN nxt env e
         ⊛ unembedN (suc nxt) (nxt ∷ env) (P nxt)
         ⊛ unembedN nxt env z
         ⊛ unembedN (suc nxt) (nxt ∷ env) (s nxt)
  unembedN nxt env (mEmp e P)     =
    mEmp <$> unembedN nxt env e
         ⊛ unembedN (suc nxt) (nxt ∷ env) (P nxt)
  unembedN nxt env (mUnit e P u)  =
    mUnit <$> unembedN nxt env e
          ⊛ unembedN (suc nxt) (nxt ∷ env) (P nxt)
          ⊛ unembedN nxt env u
  unembedN nxt env (idt A a b)    =
    idt <$> unembedN nxt env A ⊛ unembedN nxt env a ⊛ unembedN nxt env b
  unembedN nxt env rfl            = ok rfl
  unembedN nxt env (rwt e P t)    =
    rwt <$> unembedN nxt env e
        ⊛ unembedN (suc nxt) (nxt ∷ env) (P nxt)
        ⊛ unembedN nxt env t
  unembedN nxt env (def i)        = ok (def i)
  unembedN nxt env (ann e A)      =
    ann <$> unembedN nxt env e ⊛ unembedN nxt env A
  unembedN nxt env (prod A B)     =
    prod <$> unembedN nxt env A ⊛ unembedN nxt env B
  unembedN nxt env (pair a b)     =
    pair <$> unembedN nxt env a ⊛ unembedN nxt env b
  unembedN nxt env (letp e t)     =
    letp <$> unembedN nxt env e
         ⊛ unembedN (suc (suc nxt)) (suc nxt ∷ nxt ∷ env) (t nxt (suc nxt))
  unembedN nxt env (nu F)         =
    nu <$> unembedN (suc nxt) (nxt ∷ env) (F nxt)
  unembedN nxt env (unf s f)      =
    unf <$> unembedN nxt env s ⊛ unembedN nxt env f
  unembedN nxt env (ucons s)      = ucons <$> unembedN nxt env s
  unembedN nxt env i64            = ok i64
  unembedN nxt env f32ty          = ok f32ty
  unembedN nxt env (tensor d s)   =
    tensor <$> unembedN nxt env d ⊛ unembedN nxt env s
  unembedN nxt env (addi x y)     =
    addi <$> unembedN nxt env x ⊛ unembedN nxt env y
  unembedN nxt env (muli x y)     =
    muli <$> unembedN nxt env x ⊛ unembedN nxt env y
  unembedN nxt env (addt t u)     =
    addt <$> unembedN nxt env t ⊛ unembedN nxt env u
  unembedN nxt env (toi64 t)      = toi64 <$> unembedN nxt env t
  unembedN nxt env (packi x y)    =
    packi <$> unembedN nxt env x ⊛ unembedN nxt env y

unembed : PTm ℕ → Result (Tm 0)
unembed t = unembedN 0 [] t

unembed∀ : (∀ {V} → PTm V) → Result (Tm 0)
unembed∀ t = unembed t
