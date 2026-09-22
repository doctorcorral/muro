------------------------------------------------------------------------
-- Conversion for the ⊢ fragment: one-step reduction ⟶, its closure ⟶*,
-- and the equivalence ≈ that reduction generates. No fuel.
--
-- ⟶ is the weak strategy of Check.whnf, plus reduction in the argument
-- of a stuck application and under su (the positions Check.conv
-- compares after whnf):
--   δ    def i unfolds when allowedDef permits the mode
--   β    app (lam _ _ t) a ⟶ inst t a
--   ι    mNat ze / mNat (su _) / mUnit one / rwt rfl
--   ann  ann e A ⟶ e
--   congruence: app function; app argument once the function is
--   neutral; su; the scrutinee of mNat / mUnit / mEmp; the equation
--   of rwt.
--
-- ≈ does not contain: reduction under λ, Π, idt, motives, or branches;
-- η; any rule for data / ν / products / Nx (those terms are inert
-- neutrals here). Check.conv is wider: it compares subterms after whnf.
--
-- ⟶ is deterministic (det). Hence ≈ is joinability (≈→join), and two
-- normal forms are convertible only when equal (≈-nf). Consistency
-- uses that inversion principle; it needs no confluence proof.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Convert where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst using (inst; closed)
open import Muro.Env

ok-inj : ∀ {A : Set} {x y : A} → ok x ≡ ok y → x ≡ y
ok-inj refl = refl

------------------------------------------------------------------------
-- Terms outside the fragment. They never reduce.
------------------------------------------------------------------------

data Foreign {n} : Tm n → Set where
  f-dty    : ∀ {i} → Foreign (dty i)
  f-ctor   : ∀ {i j} → Foreign (ctor i j)
  f-mData  : ∀ {e P bs} → Foreign (mData e P bs)
  f-prod   : ∀ {A B} → Foreign (prod A B)
  f-pair   : ∀ {a b} → Foreign (pair a b)
  f-fst    : ∀ {t} → Foreign (fst t)
  f-snd    : ∀ {t} → Foreign (snd t)
  f-nu     : ∀ {F} → Foreign (nu F)
  f-unf    : ∀ {s f} → Foreign (unf s f)
  f-ucons  : ∀ {s} → Foreign (ucons s)
  f-i64    : Foreign i64
  f-f32ty  : Foreign f32ty
  f-tensor : ∀ {d s} → Foreign (tensor d s)
  f-addi   : ∀ {x y} → Foreign (addi x y)
  f-muli   : ∀ {x y} → Foreign (muli x y)
  f-addt   : ∀ {t u} → Foreign (addt t u)
  f-toi64  : ∀ {t} → Foreign (toi64 t)
  f-packi  : ∀ {x y} → Foreign (packi x y)

natCanon : ∀ {n} → Tm n → Bool
natCanon ze     = true
natCanon (su _) = true
natCanon _      = false

------------------------------------------------------------------------
-- Neutral and normal terms for this strategy. Ne is the side condition
-- for reducing an application argument; Nf is what Consistency inverts.
-- Neither is complete: some ill-typed terms are stuck without being Ne.
------------------------------------------------------------------------

data Ne (σ : Sig) (m : Mode) {n} : Tm n → Set
data Nf (σ : Sig) (m : Mode) {n} : Tm n → Set

data Ne σ m where
  ne-var     : ∀ {x} → Ne σ m (var x)
  ne-def     : ∀ {i}
    → (∀ {d} → lookupDef σ i ≡ ok d → allowedDef (Def.dmode d) m ≡ true → ⊥)
    → Ne σ m (def i)
  ne-app     : ∀ {f a} → Ne σ m f → Nf σ m a → Ne σ m (app f a)
  ne-mNat    : ∀ {e P z s} → Ne σ m e → Ne σ m (mNat e P z s)
  ne-mUnit   : ∀ {e P u} → Ne σ m e → Ne σ m (mUnit e P u)
  ne-mEmp    : ∀ {e P} → Ne σ m e → Ne σ m (mEmp e P)
  ne-rwt     : ∀ {eq P t} → Ne σ m eq → Ne σ m (rwt eq P t)
  ne-foreign : ∀ {t} → Foreign t → Ne σ m t

data Nf σ m where
  nf-ne    : ∀ {t} → Ne σ m t → Nf σ m t
  nf-typ   : Nf σ m typ
  nf-pi    : ∀ {q A B} → Nf σ m (pi q A B)
  nf-lam   : ∀ {q A t} → Nf σ m (lam q A t)
  nf-nat   : Nf σ m nat
  nf-ze    : Nf σ m ze
  nf-su    : ∀ {t} → Nf σ m t → Nf σ m (su t)
  nf-unit  : Nf σ m unit
  nf-one   : Nf σ m one
  nf-empty : Nf σ m empty
  nf-idt   : ∀ {A a b} → Nf σ m (idt A a b)
  nf-rfl   : Nf σ m rfl

------------------------------------------------------------------------
-- One-step reduction.
------------------------------------------------------------------------

infix 3 _⊢[_]_⟶_ _⊢[_]_⟶*_ _⊢[_]_≈_

data _⊢[_]_⟶_ (σ : Sig) (m : Mode) {n} : Tm n → Tm n → Set where
  δ : ∀ {i d}
    → lookupDef σ i ≡ ok d
    → allowedDef (Def.dmode d) m ≡ true
    → σ ⊢[ m ] def i ⟶ closed (Def.dbody d)

  β : ∀ {q A t a}
    → σ ⊢[ m ] app (lam q A t) a ⟶ inst t a

  app-f : ∀ {f f′ a}
    → σ ⊢[ m ] f ⟶ f′
    → σ ⊢[ m ] app f a ⟶ app f′ a

  app-a : ∀ {f a a′}
    → Ne σ m f
    → σ ⊢[ m ] a ⟶ a′
    → σ ⊢[ m ] app f a ⟶ app f a′

  su-c : ∀ {t t′}
    → σ ⊢[ m ] t ⟶ t′
    → σ ⊢[ m ] su t ⟶ su t′

  ιz : ∀ {P z s}
    → σ ⊢[ m ] mNat ze P z s ⟶ z

  ιs : ∀ {u P z s}
    → σ ⊢[ m ] mNat (su u) P z s ⟶ inst s u

  mNat-e : ∀ {e e′ P z s}
    → natCanon e ≡ false
    → σ ⊢[ m ] e ⟶ e′
    → σ ⊢[ m ] mNat e P z s ⟶ mNat e′ P z s

  ιtt : ∀ {P u}
    → σ ⊢[ m ] mUnit one P u ⟶ u

  mUnit-e : ∀ {e e′ P u}
    → σ ⊢[ m ] e ⟶ e′
    → σ ⊢[ m ] mUnit e P u ⟶ mUnit e′ P u

  mEmp-e : ∀ {e e′ P}
    → σ ⊢[ m ] e ⟶ e′
    → σ ⊢[ m ] mEmp e P ⟶ mEmp e′ P

  ιrfl : ∀ {P t}
    → σ ⊢[ m ] rwt rfl P t ⟶ t

  rwt-e : ∀ {eq eq′ P t}
    → σ ⊢[ m ] eq ⟶ eq′
    → σ ⊢[ m ] rwt eq P t ⟶ rwt eq′ P t

  ann-e : ∀ {e A}
    → σ ⊢[ m ] ann e A ⟶ e

-- A term that steps is either su _ or not a Nat constructor.
step-natCanon : ∀ {σ m n} {e e′ : Tm n}
  → σ ⊢[ m ] e ⟶ e′ → (natCanon e ≡ false) ⊎ (∃ λ u → e ≡ su u)
step-natCanon (δ _ _)      = inj₁ refl
step-natCanon β            = inj₁ refl
step-natCanon (app-f _)    = inj₁ refl
step-natCanon (app-a _ _)  = inj₁ refl
step-natCanon (su-c _)     = inj₂ (_ , refl)
step-natCanon ιz           = inj₁ refl
step-natCanon ιs           = inj₁ refl
step-natCanon (mNat-e _ _) = inj₁ refl
step-natCanon ιtt          = inj₁ refl
step-natCanon (mUnit-e _)  = inj₁ refl
step-natCanon (mEmp-e _)   = inj₁ refl
step-natCanon ιrfl         = inj₁ refl
step-natCanon (rwt-e _)    = inj₁ refl
step-natCanon ann-e        = inj₁ refl

------------------------------------------------------------------------
-- Normal forms do not step.
------------------------------------------------------------------------

foreign-no-step : ∀ {σ m n} {t u : Tm n} → Foreign t → σ ⊢[ m ] t ⟶ u → ⊥
foreign-no-step f-dty    ()
foreign-no-step f-ctor   ()
foreign-no-step f-mData  ()
foreign-no-step f-prod   ()
foreign-no-step f-pair   ()
foreign-no-step f-fst    ()
foreign-no-step f-snd    ()
foreign-no-step f-nu     ()
foreign-no-step f-unf    ()
foreign-no-step f-ucons  ()
foreign-no-step f-i64    ()
foreign-no-step f-f32ty  ()
foreign-no-step f-tensor ()
foreign-no-step f-addi   ()
foreign-no-step f-muli   ()
foreign-no-step f-addt   ()
foreign-no-step f-toi64  ()
foreign-no-step f-packi  ()

ne-no-step : ∀ {σ m n} {t u : Tm n} → Ne σ m t → σ ⊢[ m ] t ⟶ u → ⊥
nf-no-step : ∀ {σ m n} {t u : Tm n} → Nf σ m t → σ ⊢[ m ] t ⟶ u → ⊥

ne-no-step ne-var ()
ne-no-step (ne-def stuck) (δ lk al) = stuck lk al
ne-no-step (ne-app (ne-foreign ()) _) β
ne-no-step (ne-app nf _) (app-f s) = ne-no-step nf s
ne-no-step (ne-app _ na) (app-a _ s) = nf-no-step na s
ne-no-step (ne-mNat (ne-foreign ())) ιz
ne-no-step (ne-mNat (ne-foreign ())) ιs
ne-no-step (ne-mNat ne) (mNat-e _ s) = ne-no-step ne s
ne-no-step (ne-mUnit (ne-foreign ())) ιtt
ne-no-step (ne-mUnit ne) (mUnit-e s) = ne-no-step ne s
ne-no-step (ne-mEmp ne) (mEmp-e s) = ne-no-step ne s
ne-no-step (ne-rwt (ne-foreign ())) ιrfl
ne-no-step (ne-rwt ne) (rwt-e s) = ne-no-step ne s
ne-no-step (ne-foreign f) s = foreign-no-step f s

nf-no-step (nf-ne ne) s = ne-no-step ne s
nf-no-step nf-typ ()
nf-no-step nf-pi ()
nf-no-step nf-lam ()
nf-no-step nf-nat ()
nf-no-step nf-ze ()
nf-no-step (nf-su nf) (su-c s) = nf-no-step nf s
nf-no-step nf-unit ()
nf-no-step nf-one ()
nf-no-step nf-empty ()
nf-no-step nf-idt ()
nf-no-step nf-rfl ()

------------------------------------------------------------------------
-- Determinism.
------------------------------------------------------------------------

det : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⟶ u → σ ⊢[ m ] t ⟶ v → u ≡ v
det (δ lk _) (δ lk′ _) with ok-inj (trans (sym lk) lk′)
... | refl = refl
det β β = refl
det β (app-f ())
det β (app-a (ne-foreign ()) _)
det (app-f ()) β
det (app-f s) (app-f s′) = cong (λ f → app f _) (det s s′)
det (app-f s) (app-a ne _) = ⊥-elim (ne-no-step ne s)
det (app-a (ne-foreign ()) _) β
det (app-a ne _) (app-f s) = ⊥-elim (ne-no-step ne s)
det (app-a _ s) (app-a _ s′) = cong (app _) (det s s′)
det (su-c s) (su-c s′) = cong su (det s s′)
det ιz ιz = refl
det ιz (mNat-e _ ())
det ιs ιs = refl
det ιs (mNat-e () _)
det (mNat-e _ ()) ιz
det (mNat-e () _) ιs
det (mNat-e _ s) (mNat-e _ s′) = cong (λ e → mNat e _ _ _) (det s s′)
det ιtt ιtt = refl
det ιtt (mUnit-e ())
det (mUnit-e ()) ιtt
det (mUnit-e s) (mUnit-e s′) = cong (λ e → mUnit e _ _) (det s s′)
det (mEmp-e s) (mEmp-e s′) = cong (λ e → mEmp e _) (det s s′)
det ιrfl ιrfl = refl
det ιrfl (rwt-e ())
det (rwt-e ()) ιrfl
det (rwt-e s) (rwt-e s′) = cong (λ e → rwt e _ _) (det s s′)
det ann-e ann-e = refl

------------------------------------------------------------------------
-- Reflexive-transitive closure.
------------------------------------------------------------------------

data _⊢[_]_⟶*_ (σ : Sig) (m : Mode) {n} : Tm n → Tm n → Set where
  ⟶*-refl : ∀ {t} → σ ⊢[ m ] t ⟶* t
  ⟶*-step : ∀ {t u v} → σ ⊢[ m ] t ⟶ u → σ ⊢[ m ] u ⟶* v → σ ⊢[ m ] t ⟶* v

⟶*-trans : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⟶* u → σ ⊢[ m ] u ⟶* v → σ ⊢[ m ] t ⟶* v
⟶*-trans ⟶*-refl r = r
⟶*-trans (⟶*-step s r) r′ = ⟶*-step s (⟶*-trans r r′)

-- Two reduction sequences from one term are ordered.
det* : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⟶* u → σ ⊢[ m ] t ⟶* v
  → (σ ⊢[ m ] u ⟶* v) ⊎ (σ ⊢[ m ] v ⟶* u)
det* ⟶*-refl r = inj₁ r
det* (⟶*-step s r) ⟶*-refl = inj₂ (⟶*-step s r)
det* (⟶*-step s r) (⟶*-step s′ r′) with det s s′
... | refl = det* r r′

nf-⟶* : ∀ {σ m n} {t u : Tm n} → Nf σ m t → σ ⊢[ m ] t ⟶* u → u ≡ t
nf-⟶* _ ⟶*-refl = refl
nf-⟶* nf (⟶*-step s _) = ⊥-elim (nf-no-step nf s)

------------------------------------------------------------------------
-- Conversion: the equivalence generated by ⟶.
------------------------------------------------------------------------

data _⊢[_]_≈_ (σ : Sig) (m : Mode) {n} : Tm n → Tm n → Set where
  ≈-step  : ∀ {t u} → σ ⊢[ m ] t ⟶ u → σ ⊢[ m ] t ≈ u
  ≈-refl  : ∀ {t} → σ ⊢[ m ] t ≈ t
  ≈-sym   : ∀ {t u} → σ ⊢[ m ] t ≈ u → σ ⊢[ m ] u ≈ t
  ≈-trans : ∀ {t u v} → σ ⊢[ m ] t ≈ u → σ ⊢[ m ] u ≈ v → σ ⊢[ m ] t ≈ v

⟶*→≈ : ∀ {σ m n} {t u : Tm n} → σ ⊢[ m ] t ⟶* u → σ ⊢[ m ] t ≈ u
⟶*→≈ ⟶*-refl = ≈-refl
⟶*→≈ (⟶*-step s r) = ≈-trans (≈-step s) (⟶*→≈ r)

-- Because ⟶ is deterministic, convertible terms have a common reduct.
≈→join : ∀ {σ m n} {t u : Tm n}
  → σ ⊢[ m ] t ≈ u
  → ∃ λ v → (σ ⊢[ m ] t ⟶* v) × (σ ⊢[ m ] u ⟶* v)
≈→join (≈-step s) = _ , ⟶*-step s ⟶*-refl , ⟶*-refl
≈→join ≈-refl = _ , ⟶*-refl , ⟶*-refl
≈→join (≈-sym c) with ≈→join c
... | v , a , b = v , b , a
≈→join (≈-trans c c′) with ≈→join c | ≈→join c′
... | v , tv , uv | w , uw , sw with det* uv uw
...   | inj₁ vw = w , ⟶*-trans tv vw , sw
...   | inj₂ wv = v , tv , ⟶*-trans sw wv

------------------------------------------------------------------------
-- Inversion: a normal form is convertible only to what reduces to it.
------------------------------------------------------------------------

≈-nf-⟶* : ∀ {σ m n} {t u : Tm n}
  → Nf σ m u → σ ⊢[ m ] t ≈ u → σ ⊢[ m ] t ⟶* u
≈-nf-⟶* nfu c with ≈→join c
... | v , tv , uv = subst (λ w → _ ⊢[ _ ] _ ⟶* w) (nf-⟶* nfu uv) tv

≈-nf : ∀ {σ m n} {t u : Tm n}
  → Nf σ m t → Nf σ m u → σ ⊢[ m ] t ≈ u → t ≡ u
≈-nf nft nfu c with ≈→join c
... | v , tv , uv = trans (sym (nf-⟶* nft tv)) (nf-⟶* nfu uv)
