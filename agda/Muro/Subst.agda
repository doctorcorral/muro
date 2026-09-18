------------------------------------------------------------------------
-- Substitution on de Bruijn terms, plus toPHOAS / unembed.
------------------------------------------------------------------------

module Muro.Subst where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)

open import Muro.Base
open import Muro.Syntax

------------------------------------------------------------------------
-- Renaming and substitution (de Bruijn).
------------------------------------------------------------------------

lift : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
lift ρ zero    = zero
lift ρ (suc i) = suc (ρ i)

ren : ∀ {n m} → (Fin n → Fin m) → Tm n → Tm m
ren ρ (var i)       = var (ρ i)
ren ρ typ           = typ
ren ρ (pi q A B)    = pi q (ren ρ A) (ren (lift ρ) B)
ren ρ (lam q A t)   = lam q (ren ρ A) (ren (lift ρ) t)
ren ρ (app f a)     = app (ren ρ f) (ren ρ a)
ren ρ nat           = nat
ren ρ ze            = ze
ren ρ (su t)        = su (ren ρ t)
ren ρ unit          = unit
ren ρ one           = one
ren ρ empty         = empty
ren ρ (mNat e P z s)= mNat (ren ρ e) (ren (lift ρ) P) (ren ρ z) (ren (lift ρ) s)
ren ρ (mEmp e P)    = mEmp (ren ρ e) (ren (lift ρ) P)
ren ρ (mUnit e P u) = mUnit (ren ρ e) (ren (lift ρ) P) (ren ρ u)
ren ρ (idt A a b)   = idt (ren ρ A) (ren ρ a) (ren ρ b)
ren ρ rfl           = rfl
ren ρ (rwt e P t)   = rwt (ren ρ e) (ren (lift ρ) P) (ren ρ t)
ren ρ (def i)       = def i
ren ρ (ann e A)     = ann (ren ρ e) (ren ρ A)

wk : ∀ {n} → Tm n → Tm (suc n)
wk = ren suc

fromZero : ∀ {n} → Fin 0 → Fin n
fromZero ()

closed : ∀ {n} → Tm 0 → Tm n
closed = ren fromZero

lifts : ∀ {n m} → (Fin n → Tm m) → Fin (suc n) → Tm (suc m)
lifts σ zero    = var zero
lifts σ (suc i) = wk (σ i)

sub : ∀ {n m} → (Fin n → Tm m) → Tm n → Tm m
sub σ (var i)        = σ i
sub σ typ            = typ
sub σ (pi q A B)     = pi q (sub σ A) (sub (lifts σ) B)
sub σ (lam q A t)    = lam q (sub σ A) (sub (lifts σ) t)
sub σ (app f a)      = app (sub σ f) (sub σ a)
sub σ nat            = nat
sub σ ze             = ze
sub σ (su t)         = su (sub σ t)
sub σ unit           = unit
sub σ one            = one
sub σ empty          = empty
sub σ (mNat e P z s) = mNat (sub σ e) (sub (lifts σ) P) (sub σ z) (sub (lifts σ) s)
sub σ (mEmp e P)     = mEmp (sub σ e) (sub (lifts σ) P)
sub σ (mUnit e P u)  = mUnit (sub σ e) (sub (lifts σ) P) (sub σ u)
sub σ (idt A a b)    = idt (sub σ A) (sub σ a) (sub σ b)
sub σ rfl            = rfl
sub σ (rwt e P t)    = rwt (sub σ e) (sub (lifts σ) P) (sub σ t)
sub σ (def i)        = def i
sub σ (ann e A)      = ann (sub σ e) (sub σ A)

-- Open a binder: (x. t)[u].
-- Named helper: pattern-lambdas do not compute when passed to `sub`.
instσ : ∀ {n} → Tm n → Fin (suc n) → Tm n
instσ u zero    = u
instσ u (suc i) = var i

inst : ∀ {n} → Tm (suc n) → Tm n → Tm n
inst t u = sub (instσ u) t

------------------------------------------------------------------------
-- toPHOAS : de Bruijn → PHOAS
------------------------------------------------------------------------

toPHOAS : ∀ {n} {V : Set} → (Fin n → V) → Tm n → PTm V
toPHOAS ρ (var i)        = var (ρ i)
toPHOAS ρ typ            = typ
toPHOAS ρ (pi q A B)     = pi q (toPHOAS ρ A) (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) B)
toPHOAS ρ (lam q A t)    = lam q (toPHOAS ρ A) (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) t)
toPHOAS ρ (app f a)      = app (toPHOAS ρ f) (toPHOAS ρ a)
toPHOAS ρ nat            = nat
toPHOAS ρ ze             = ze
toPHOAS ρ (su t)         = su (toPHOAS ρ t)
toPHOAS ρ unit           = unit
toPHOAS ρ one            = one
toPHOAS ρ empty          = empty
toPHOAS ρ (mNat e P z s) = mNat (toPHOAS ρ e)
                                (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                (toPHOAS ρ z)
                                (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) s)
toPHOAS ρ (mEmp e P)     = mEmp (toPHOAS ρ e)
                                (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
toPHOAS ρ (mUnit e P u)  = mUnit (toPHOAS ρ e)
                                 (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                 (toPHOAS ρ u)
toPHOAS ρ (idt A a b)    = idt (toPHOAS ρ A) (toPHOAS ρ a) (toPHOAS ρ b)
toPHOAS ρ rfl            = rfl
toPHOAS ρ (rwt e P t)    = rwt (toPHOAS ρ e)
                               (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                               (toPHOAS ρ t)
toPHOAS ρ (def i)        = def i
toPHOAS ρ (ann e A)      = ann (toPHOAS ρ e) (toPHOAS ρ A)

toPHOAS0 : ∀ {V : Set} → Tm 0 → PTm V
toPHOAS0 t = toPHOAS (λ ()) t

------------------------------------------------------------------------
-- unembed : PHOAS → de Bruijn
--
-- Apply each PHOAS binder to a fresh ℕ and read the name stack back as
-- de Bruijn indices. Parametric PHOAS terms (the only well-formed ones)
-- do not inspect the ℕ.
--
-- Termination: each recursive call is on a structurally smaller PTm
-- after applying a binder to a name; Agda cannot see that, so we mark
-- the function. The checker itself is fuel-based and does not use this.
------------------------------------------------------------------------

eqNat : ℕ → ℕ → Bool
eqNat zero    zero    = true
eqNat (suc m) (suc n) = eqNat m n
eqNat _       _       = false

findName : ∀ {n} → ℕ → Vec ℕ n → Result (Fin n)
findName x [] = fail "unembed: free name"
findName x (y ∷ ys) with eqNat x y
... | true  = ok zero
... | false = suc <$> findName x ys

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

unembed : PTm ℕ → Result (Tm 0)
unembed t = unembedN 0 [] t

-- Closed polymorphic PHOAS → de Bruijn.
unembed∀ : (∀ {V} → PTm V) → Result (Tm 0)
unembed∀ t = unembed t
