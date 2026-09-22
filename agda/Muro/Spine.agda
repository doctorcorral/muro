------------------------------------------------------------------------
-- Application spines. Spine h as e says e is h applied to as, left to
-- right (e ≡ appsFrom h as). Data uses it for constructor applications
-- ctor i j a₁ … aₙ and data types dty i p₁ … pₙ, whose heads are rigid:
-- they are not λ, so a spine only reduces to a spine with the same head.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Spine where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env using (lookupList)

-- The two list facts used, proved here to keep the import footprint small.
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

data Spine {n} (h : Tm n) : List (Tm n) → Tm n → Set where
  sp-[]   : Spine h [] h
  sp-snoc : ∀ {as f a} → Spine h as f → Spine h (as ++ (a ∷ [])) (app f a)

------------------------------------------------------------------------
-- Spine and appsFrom.
------------------------------------------------------------------------

appsFrom-snoc : ∀ {n} (f : Tm n) as a
  → appsFrom f (as ++ (a ∷ [])) ≡ app (appsFrom f as) a
appsFrom-snoc f [] a = refl
appsFrom-snoc f (b ∷ as) a = appsFrom-snoc (app f b) as a

appsFrom-++ : ∀ {n} (f : Tm n) as bs
  → appsFrom f (as ++ bs) ≡ appsFrom (appsFrom f as) bs
appsFrom-++ f [] bs = refl
appsFrom-++ f (a ∷ as) bs = appsFrom-++ (app f a) as bs

Spine-≡ : ∀ {n} {h : Tm n} {as e} → Spine h as e → e ≡ appsFrom h as
Spine-≡ sp-[] = refl
Spine-≡ (sp-snoc {as = as} {a = a} sp) =
  trans (cong (λ f → app f a) (Spine-≡ sp)) (sym (appsFrom-snoc _ as a))

Spine-appsFrom′ : ∀ {n} {h : Tm n} as {as₀ f}
  → Spine h as₀ f → Spine h (as₀ ++ as) (appsFrom f as)
Spine-appsFrom′ [] {as₀} sp rewrite ++-identityʳ as₀ = sp
Spine-appsFrom′ (a ∷ as) {as₀} sp =
  subst (λ xs → Spine _ xs _) (++-assoc as₀ (a ∷ []) as)
    (Spine-appsFrom′ as (sp-snoc sp))

Spine-appsFrom : ∀ {n} (h : Tm n) as → Spine h as (appsFrom h as)
Spine-appsFrom h as = Spine-appsFrom′ as sp-[]

Spine-++ : ∀ {n} {h : Tm n} {as e} bs
  → Spine h as e → Spine h (as ++ bs) (appsFrom e bs)
Spine-++ bs sp = Spine-appsFrom′ bs sp

------------------------------------------------------------------------
-- Reading a spine off a term. unspine e = (h , as) with e ≡ appsFrom h as
-- and h not an application.
------------------------------------------------------------------------

unspine-go : ∀ {n} → Tm n → List (Tm n) → Tm n × List (Tm n)
unspine-go (app f a) acc = unspine-go f (a ∷ acc)
unspine-go h acc = h , acc

unspine : ∀ {n} → Tm n → Tm n × List (Tm n)
unspine e = unspine-go e []

-- Heads that unspine leaves alone.
Head : ∀ {n} → Tm n → Set
Head h = ∀ acc → unspine-go h acc ≡ (h , acc)

head-ctor : ∀ {n i j} → Head {n} (ctor i j)
head-ctor acc = refl

head-dty : ∀ {n i} → Head {n} (dty i)
head-dty acc = refl

Spine→unspine-go : ∀ {n} {h : Tm n} {as e} → Head h → Spine h as e
  → ∀ acc → unspine-go e acc ≡ (h , as ++ acc)
Spine→unspine-go hd sp-[] acc = hd acc
Spine→unspine-go hd (sp-snoc {as = as} {a = a} sp) acc =
  trans (Spine→unspine-go hd sp (a ∷ acc))
    (cong (λ xs → _ , xs) (sym (++-assoc as (a ∷ []) acc)))

Spine→unspine : ∀ {n} {h : Tm n} {as e} → Head h → Spine h as e
  → unspine e ≡ (h , as)
Spine→unspine {as = as} hd sp =
  trans (Spine→unspine-go hd sp []) (cong (λ xs → _ , xs) (++-identityʳ as))

unspine→Spine : ∀ {n} (e : Tm n) acc {h as} → unspine-go e acc ≡ (h , as)
  → ∃ λ as₀ → (as ≡ as₀ ++ acc) × Spine h as₀ e
unspine→Spine (app f a) acc eq with unspine→Spine f (a ∷ acc) eq
... | as₀ , eq′ , sp = as₀ ++ (a ∷ []) , trans eq′ (sym (++-assoc as₀ (a ∷ []) acc)) , sp-snoc sp
unspine→Spine (var _) acc refl = [] , refl , sp-[]
unspine→Spine (typ) acc refl = [] , refl , sp-[]
unspine→Spine (pi _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (lam _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (nat) acc refl = [] , refl , sp-[]
unspine→Spine (ze) acc refl = [] , refl , sp-[]
unspine→Spine (su _) acc refl = [] , refl , sp-[]
unspine→Spine (unit) acc refl = [] , refl , sp-[]
unspine→Spine (one) acc refl = [] , refl , sp-[]
unspine→Spine (empty) acc refl = [] , refl , sp-[]
unspine→Spine (dty _) acc refl = [] , refl , sp-[]
unspine→Spine (ctor _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mData _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mNat _ _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mEmp _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mUnit _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (idt _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (rfl) acc refl = [] , refl , sp-[]
unspine→Spine (rwt _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (def _) acc refl = [] , refl , sp-[]
unspine→Spine (ann _ _) acc refl = [] , refl , sp-[]
unspine→Spine (prod _ _) acc refl = [] , refl , sp-[]
unspine→Spine (pair _ _) acc refl = [] , refl , sp-[]
unspine→Spine (fst _) acc refl = [] , refl , sp-[]
unspine→Spine (snd _) acc refl = [] , refl , sp-[]
unspine→Spine (nu _) acc refl = [] , refl , sp-[]
unspine→Spine (unf _ _) acc refl = [] , refl , sp-[]
unspine→Spine (ucons _) acc refl = [] , refl , sp-[]
unspine→Spine (i64) acc refl = [] , refl , sp-[]
unspine→Spine (f32ty) acc refl = [] , refl , sp-[]
unspine→Spine (tensor _ _) acc refl = [] , refl , sp-[]
unspine→Spine (addi _ _) acc refl = [] , refl , sp-[]
unspine→Spine (muli _ _) acc refl = [] , refl , sp-[]
unspine→Spine (addt _ _) acc refl = [] , refl , sp-[]
unspine→Spine (toi64 _) acc refl = [] , refl , sp-[]
unspine→Spine (packi _ _) acc refl = [] , refl , sp-[]

unspine→Spine′ : ∀ {n} {e h : Tm n} {as} → unspine e ≡ (h , as) → Spine h as e
unspine→Spine′ {e = e} eq with unspine→Spine e [] eq
... | as₀ , eq′ , sp rewrite eq′ | ++-identityʳ as₀ = sp

-- Spines with rigid heads are read uniquely.
Spine-unique : ∀ {n} {h h′ : Tm n} {as as′ e} → Head h → Head h′
  → Spine h as e → Spine h′ as′ e → (h ≡ h′) × (as ≡ as′)
Spine-unique hd hd′ sp sp′
  with trans (sym (Spine→unspine hd sp)) (Spine→unspine hd′ sp′)
... | refl = refl , refl

------------------------------------------------------------------------
-- Renaming and substitution.
------------------------------------------------------------------------

renList-++ : ∀ {n m} (ρ : Fin n → Fin m) (as bs : List (Tm n))
  → renList ρ (as ++ bs) ≡ renList ρ as ++ renList ρ bs
renList-++ ρ [] bs = refl
renList-++ ρ (a ∷ as) bs = cong (ren ρ a ∷_) (renList-++ ρ as bs)

subList-++ : ∀ {n m} (τ : Fin n → Tm m) (as bs : List (Tm n))
  → subList τ (as ++ bs) ≡ subList τ as ++ subList τ bs
subList-++ τ [] bs = refl
subList-++ τ (a ∷ as) bs = cong (sub τ a ∷_) (subList-++ τ as bs)

renList-length : ∀ {n m} (ρ : Fin n → Fin m) (as : List (Tm n))
  → length (renList ρ as) ≡ length as
renList-length ρ [] = refl
renList-length ρ (a ∷ as) = cong suc (renList-length ρ as)

subList-length : ∀ {n m} (τ : Fin n → Tm m) (as : List (Tm n))
  → length (subList τ as) ≡ length as
subList-length τ [] = refl
subList-length τ (a ∷ as) = cong suc (subList-length τ as)

renList-take : ∀ {n m} (ρ : Fin n → Fin m) k (as : List (Tm n))
  → renList ρ (take k as) ≡ take k (renList ρ as)
renList-take ρ zero as = refl
renList-take ρ (suc k) [] = refl
renList-take ρ (suc k) (a ∷ as) = cong (ren ρ a ∷_) (renList-take ρ k as)

subList-take : ∀ {n m} (τ : Fin n → Tm m) k (as : List (Tm n))
  → subList τ (take k as) ≡ take k (subList τ as)
subList-take τ zero as = refl
subList-take τ (suc k) [] = refl
subList-take τ (suc k) (a ∷ as) = cong (sub τ a ∷_) (subList-take τ k as)

ren-appsFrom : ∀ {n m} (ρ : Fin n → Fin m) (f : Tm n) as
  → ren ρ (appsFrom f as) ≡ appsFrom (ren ρ f) (renList ρ as)
ren-appsFrom ρ f [] = refl
ren-appsFrom ρ f (a ∷ as) = ren-appsFrom ρ (app f a) as

sub-appsFrom : ∀ {n m} (τ : Fin n → Tm m) (f : Tm n) as
  → sub τ (appsFrom f as) ≡ appsFrom (sub τ f) (subList τ as)
sub-appsFrom τ f [] = refl
sub-appsFrom τ f (a ∷ as) = sub-appsFrom τ (app f a) as

Spine-ren : ∀ {n m} (ρ : Fin n → Fin m) {h : Tm n} {as e}
  → Spine h as e → Spine (ren ρ h) (renList ρ as) (ren ρ e)
Spine-ren ρ sp-[] = sp-[]
Spine-ren ρ (sp-snoc {as = as} {a = a} sp) =
  subst (λ xs → Spine _ xs _) (sym (renList-++ ρ as (a ∷ [])))
    (sp-snoc (Spine-ren ρ sp))

Spine-sub : ∀ {n m} (τ : Fin n → Tm m) {h : Tm n} {as e}
  → Spine h as e → Spine (sub τ h) (subList τ as) (sub τ e)
Spine-sub τ sp-[] = sp-[]
Spine-sub τ (sp-snoc {as = as} {a = a} sp) =
  subst (λ xs → Spine _ xs _) (sym (subList-++ τ as (a ∷ [])))
    (sp-snoc (Spine-sub τ sp))

lookupList-ren : ∀ {n m} (ρ : Fin n → Fin m) (bs : List (Tm n)) k {b}
  → lookupList bs k ≡ ok b → lookupList (renList ρ bs) k ≡ ok (ren ρ b)
lookupList-ren ρ (b ∷ bs) zero refl = refl
lookupList-ren ρ (b ∷ bs) (suc k) eq = lookupList-ren ρ bs k eq
lookupList-ren ρ [] zero ()
lookupList-ren ρ [] (suc k) ()

lookupList-sub : ∀ {n m} (τ : Fin n → Tm m) (bs : List (Tm n)) k {b}
  → lookupList bs k ≡ ok b → lookupList (subList τ bs) k ≡ ok (sub τ b)
lookupList-sub τ (b ∷ bs) zero refl = refl
lookupList-sub τ (b ∷ bs) (suc k) eq = lookupList-sub τ bs k eq
lookupList-sub τ [] zero ()
lookupList-sub τ [] (suc k) ()
