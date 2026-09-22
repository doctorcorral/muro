------------------------------------------------------------------------
-- Soundness of the executable checker with respect to ⊢, on the ⊢
-- fragment (Muro.Frag): when Muro.Check says yes, ⊢ has a derivation.
--
-- Part 1: weak-head normalisation and conversion.
--   whnf-sound   whnf k σ t is reached from t by ⟶ (spec), and stays in
--                the fragment;
--   synEq-sound  synEq u v ≡ true → u ≡ v;
--   conv-sound   conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v.
--
-- This module imports Muro.Check, which carries TERMINATING pragmas, so
-- it cannot be --safe. Everything it relies on from the theory side
-- (Convert, Reduction, Frag, Spine, Tag) is --safe.
------------------------------------------------------------------------

module Muro.Soundness where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Tag
open import Muro.Spine
open import Muro.Frag
open import Muro.Reduction
open import Muro.Convert
open import Muro.Check
  using (whnf; dataWhnf; synEq; synEqD; synEqList; conv; convStuck; convN; convND;
         convArgs; eqFin; ctorHead; apps)

------------------------------------------------------------------------
-- ⟶* under evaluation contexts.
------------------------------------------------------------------------

app-f* : ∀ {σ m n} {f f′ a : Tm n} → σ ⊢[ m ] f ⟶* f′ → σ ⊢[ m ] app f a ⟶* app f′ a
app-f* ⟶*-refl = ⟶*-refl
app-f* (⟶*-step s r) = ⟶*-step (app-f s) (app-f* r)

mNat-e* : ∀ {σ m n} {e e′ : Tm n} {P z s} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mNat e P z s ⟶* mNat e′ P z s
mNat-e* ⟶*-refl = ⟶*-refl
mNat-e* (⟶*-step s r) = ⟶*-step (mNat-e s) (mNat-e* r)

mUnit-e* : ∀ {σ m n} {e e′ : Tm n} {P u} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mUnit e P u ⟶* mUnit e′ P u
mUnit-e* ⟶*-refl = ⟶*-refl
mUnit-e* (⟶*-step s r) = ⟶*-step (mUnit-e s) (mUnit-e* r)

mEmp-e* : ∀ {σ m n} {e e′ : Tm n} {P} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mEmp e P ⟶* mEmp e′ P
mEmp-e* ⟶*-refl = ⟶*-refl
mEmp-e* (⟶*-step s r) = ⟶*-step (mEmp-e s) (mEmp-e* r)

mData-e* : ∀ {σ m n} {e e′ : Tm n} {P bs} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mData e P bs ⟶* mData e′ P bs
mData-e* ⟶*-refl = ⟶*-refl
mData-e* (⟶*-step s r) = ⟶*-step (mData-e s) (mData-e* r)

------------------------------------------------------------------------
-- whnf. On a fragment term over a fragment signature, whnf k σ t is
-- reached from t by ⟶ in spec (all defs unfold) and is again in the
-- fragment. Fuel only decides how far the run goes.
------------------------------------------------------------------------

allowedDef-spec : ∀ d → allowedDef d spec ≡ true
allowedDef-spec run = refl
allowedDef-spec evid = refl
allowedDef-spec spec = refl

WhnfOk : Sig → ∀ {n} → Tm n → Tm n → Set
WhnfOk σ t u = (σ ⊢[ spec ] t ⟶* u) × Frag u

whnf-sound : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → WhnfOk σ t (whnf k σ t)
whnf-sound zero σ fs Ft = ⟶*-refl , Ft
-- app: β if the head normalises to a λ
whnf-sound (suc k) σ fs (f-app {f} {a} Ff Fa) with whnf k σ f | whnf-sound k σ fs Ff
... | lam _ _ t | r , f-lam _ Ft with whnf-sound k σ fs (Frag-inst Ft Fa)
...   | r′ , F′ = ⟶*-trans (app-f* r) (⟶*-step β r′) , F′
whnf-sound (suc k) σ fs (f-app Ff Fa) | (var _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | typ | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (pi _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (app _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | nat | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | ze | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (su _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | unit | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | one | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | empty | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (dty _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (ctor _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (mData _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (mNat _ _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (mEmp _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (mUnit _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (idt _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | rfl | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (rwt _ _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (def _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (ann _ _) | r , F = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) | (prod _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (pair _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (fst _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (snd _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (nu _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (unf _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (ucons _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | i64 | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | f32ty | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (tensor _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (addi _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (muli _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (addt _ _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (toi64 _) | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) | (packi _ _) | _ , ()
-- mNat: ι on ze / su
whnf-sound (suc k) σ fs (f-mNat {e} {P} {z} {s} Fe FP Fz Fs) with whnf k σ e | whnf-sound k σ fs Fe
... | ze | r , _ with whnf-sound k σ fs Fz
...   | r′ , F′ = ⟶*-trans (mNat-e* r) (⟶*-step ιz r′) , F′
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | su u | r , f-su Fu with whnf-sound k σ fs (Frag-inst Fs Fu)
...   | r′ , F′ = ⟶*-trans (mNat-e* r) (⟶*-step ιs r′) , F′
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (var _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | typ | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (pi _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (lam _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (app _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | nat | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | unit | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | one | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | empty | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (dty _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (ctor _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (mData _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (mNat _ _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (mEmp _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (mUnit _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (idt _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | rfl | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (rwt _ _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (def _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (ann _ _) | r , F = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (prod _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (pair _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (fst _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (snd _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (nu _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (unf _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (ucons _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | i64 | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | f32ty | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (tensor _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (addi _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (muli _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (addt _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (toi64 _) | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) | (packi _ _) | _ , ()
-- mUnit: ι on one
whnf-sound (suc k) σ fs (f-mUnit {e} {P} {u} Fe FP Fu) with whnf k σ e | whnf-sound k σ fs Fe
... | one | r , _ with whnf-sound k σ fs Fu
...   | r′ , F′ = ⟶*-trans (mUnit-e* r) (⟶*-step ιtt r′) , F′
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (var _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | typ | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (pi _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (lam _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (app _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | nat | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | ze | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (su _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | unit | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | empty | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (dty _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (ctor _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (mData _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (mNat _ _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (mEmp _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (mUnit _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (idt _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | rfl | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (rwt _ _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (def _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (ann _ _) | r , F = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (prod _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (pair _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (fst _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (snd _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (nu _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (unf _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (ucons _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | i64 | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | f32ty | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (tensor _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (addi _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (muli _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (addt _ _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (toi64 _) | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) | (packi _ _) | _ , ()
-- mEmp: the scrutinee only
whnf-sound (suc k) σ fs (f-mEmp Fe FP) with whnf-sound k σ fs Fe
... | r , F = mEmp-e* r , f-mEmp F FP
-- mData: ι-data when the scrutinee normalises to a constructor spine
-- with a branch
whnf-sound (suc k) σ fs (f-mData {e} {P} {bs} Fe FP Fbs) with whnf k σ e | whnf-sound k σ fs Fe
... | e′ | r , Fe′ with ctorSpine e′ in ceq
...   | nothing = mData-e* r , f-mData Fe′ FP Fbs
...   | just (i , ci , args) with lookupList bs ci in leq
...     | fail _ = mData-e* r , f-mData Fe′ FP Fbs
...     | ok b with ctorSpine-just ceq
...       | sp with whnf-sound k σ fs (Frag-appsFrom (FragL-lookup Fbs leq) (proj₂ (Frag-Spine sp Fe′)))
...         | r′ , F′ = ⟶*-trans (mData-e* r) (⟶*-step (ι-data sp leq) r′) , F′
-- δ: every def unfolds in spec
whnf-sound (suc k) σ fs (f-def {i}) with lookupDef σ i in leq
... | fail _ = ⟶*-refl , f-def
... | ok d with whnf-sound k σ fs (Frag-closed (proj₂ (FragSig.defs fs i d leq)))
...   | r , F = ⟶*-step (δ leq (allowedDef-spec _)) r , F
-- annotations are dropped
whnf-sound (suc k) σ fs (f-ann Fe FA) with whnf-sound k σ fs Fe
... | r , F = ⟶*-step ann-e r , F
-- everything else is already weak-head normal for whnf
whnf-sound (suc k) σ fs f-var = ⟶*-refl , f-var
whnf-sound (suc k) σ fs f-typ = ⟶*-refl , f-typ
whnf-sound (suc k) σ fs (f-pi FA FB) = ⟶*-refl , f-pi FA FB
whnf-sound (suc k) σ fs (f-lam FA Ft) = ⟶*-refl , f-lam FA Ft
whnf-sound (suc k) σ fs f-nat = ⟶*-refl , f-nat
whnf-sound (suc k) σ fs f-ze = ⟶*-refl , f-ze
whnf-sound (suc k) σ fs (f-su Ft) = ⟶*-refl , f-su Ft
whnf-sound (suc k) σ fs f-unit = ⟶*-refl , f-unit
whnf-sound (suc k) σ fs f-one = ⟶*-refl , f-one
whnf-sound (suc k) σ fs f-empty = ⟶*-refl , f-empty
whnf-sound (suc k) σ fs f-dty = ⟶*-refl , f-dty
whnf-sound (suc k) σ fs f-ctor = ⟶*-refl , f-ctor
whnf-sound (suc k) σ fs (f-idt FA Fa Fb) = ⟶*-refl , f-idt FA Fa Fb
whnf-sound (suc k) σ fs f-rfl = ⟶*-refl , f-rfl
whnf-sound (suc k) σ fs (f-rwt Fe FP Ft) = ⟶*-refl , f-rwt Fe FP Ft

whnf-⟶* : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → σ ⊢[ spec ] t ⟶* whnf k σ t
whnf-⟶* k σ fs Ft = proj₁ (whnf-sound k σ fs Ft)

whnf-≈ : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → σ ⊢[ spec ] t ≈ whnf k σ t
whnf-≈ k σ fs Ft = ⟶*→≈ (whnf-⟶* k σ fs Ft)

whnf-Frag : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → Frag (whnf k σ t)
whnf-Frag k σ fs Ft = proj₂ (whnf-sound k σ fs Ft)
