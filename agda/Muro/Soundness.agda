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

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Tag
open import Muro.Spine
open import Muro.Frag
open import Muro.Reduction
open import Muro.Convert
open import Muro.Data hiding (subst₂)
open import Muro.Check
  using (whnf; dataWhnf; synEq; synEqD; synEqList; conv; convStuck; convN; convND;
         convArgs; eqFin; ctorHead; apps; viewPi; viewId; viewData; splitData;
         isData; allData; dataParamsData; instParams)

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

------------------------------------------------------------------------
-- Booleans and Results.
------------------------------------------------------------------------

∧-true : ∀ {a b} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true {true} {true} refl = refl , refl

∧-true₃ : ∀ {a b c} → a ∧ b ∧ c ≡ true → (a ≡ true) × (b ≡ true) × (c ≡ true)
∧-true₃ eq with ∧-true eq
... | e₁ , e = e₁ , ∧-true e

∧-true₄ : ∀ {a b c d} → a ∧ b ∧ c ∧ d ≡ true
  → (a ≡ true) × (b ≡ true) × (c ≡ true) × (d ≡ true)
∧-true₄ eq with ∧-true eq
... | e₁ , e = e₁ , ∧-true₃ e

≡ᵇ-sound : ∀ {i j} → (i ≡ᵇ j) ≡ true → i ≡ j
≡ᵇ-sound {i} {j} eq = ≡ᵇ⇒≡ i j (subst T (sym eq) tt)

eqFin-sound : ∀ {n} (i j : Fin n) → eqFin i j ≡ true → i ≡ j
eqFin-sound zero zero _ = refl
eqFin-sound (suc i) (suc j) eq = cong suc (eqFin-sound i j eq)

eqQty-sound : ∀ q q′ → eqQty q q′ ≡ true → q ≡ q′
eqQty-sound affine affine _ = refl
eqQty-sound reuse reuse _ = refl
eqQty-sound erased erased _ = refl

guard-ok : ∀ {s b} → guard s b ≡ ok tt → b ≡ true
guard-ok {b = true} _ = refl

>>-ok : ∀ {A B : Set} {r : Result A} {r′ : Result B} {x}
  → (r >> r′) ≡ ok x → (∃ λ y → r ≡ ok y) × (r′ ≡ ok x)
>>-ok {r = ok y} eq = (y , refl) , eq

-- (a >> b) >> c ≡ ok, and so on, read from the left.
>>-ok₂ : ∀ {A B C : Set} {r : Result A} {r′ : Result B} {r″ : Result C} {x}
  → (r >> r′ >> r″) ≡ ok x
  → (∃ λ y → r ≡ ok y) × (∃ λ y → r′ ≡ ok y) × (r″ ≡ ok x)
>>-ok₂ eq with >>-ok eq
... | e₁₂ , e₃ with >>-ok (proj₂ e₁₂)
...   | e₁ , e₂ = e₁ , (_ , e₂) , e₃

>>-ok₃ : ∀ {A B C D : Set} {r : Result A} {r′ : Result B} {r″ : Result C} {r‴ : Result D} {x}
  → (r >> r′ >> r″ >> r‴) ≡ ok x
  → (∃ λ y → r ≡ ok y) × (∃ λ y → r′ ≡ ok y) × (∃ λ y → r″ ≡ ok y) × (r‴ ≡ ok x)
>>-ok₃ eq with >>-ok eq
... | e , e₄ with >>-ok₂ (proj₂ e)
...   | e₁ , e₂ , e₃ = e₁ , e₂ , (_ , e₃) , e₄

ok-tt : ∀ {r : Result ⊤} {y} → r ≡ ok y → r ≡ ok tt
ok-tt eq = eq

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- synEq is syntactic equality.
------------------------------------------------------------------------

synEq-sound : ∀ {n} (u v : Tm n) → synEq u v ≡ true → u ≡ v
synEqL-sound : ∀ {n} (us vs : List (Tm n)) → synEqList us vs ≡ true → us ≡ vs
synEqD-sound : ∀ {n} {t} (u v : Tm n) → TmShape t u → TmShape t v → synEqD u v ≡ true → u ≡ v

synEq-sound u v eq with ∧-true eq
... | te , de = synEqD-sound u v (shape u) (subst (λ k → TmShape k v) (sym (≡ᵇ-sound te)) (shape v)) de

synEqL-sound [] [] _ = refl
synEqL-sound (u ∷ us) (v ∷ vs) eq with ∧-true eq
... | e , es = cong₂ _∷_ (synEq-sound u v e) (synEqL-sound us vs es)

synEqD-sound (var a) (var a′) sh-var sh-var eq = cong var (eqFin-sound a a′ eq)
synEqD-sound typ typ sh-typ sh-typ _ = refl
synEqD-sound (pi a b c) (pi a′ b′ c′) sh-pi sh-pi eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ pi (eqQty-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (lam a b c) (lam a′ b′ c′) sh-lam sh-lam eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ lam (eqQty-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (app a b) (app a′ b′) sh-app sh-app eq with ∧-true eq
... | e1 , e2 = cong₂ app (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound nat nat sh-nat sh-nat _ = refl
synEqD-sound ze ze sh-ze sh-ze _ = refl
synEqD-sound (su a) (su a′) sh-su sh-su eq = cong su (synEq-sound a a′ eq)
synEqD-sound unit unit sh-unit sh-unit _ = refl
synEqD-sound one one sh-one sh-one _ = refl
synEqD-sound empty empty sh-empty sh-empty _ = refl
synEqD-sound (dty a) (dty a′) sh-dty sh-dty eq = cong dty (≡ᵇ-sound eq)
synEqD-sound (ctor a b) (ctor a′ b′) sh-ctor sh-ctor eq with ∧-true eq
... | e1 , e2 = cong₂ ctor (≡ᵇ-sound e1) (≡ᵇ-sound e2)
synEqD-sound (mData a b c) (mData a′ b′ c′) sh-mData sh-mData eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ mData (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEqL-sound c c′ e3)
synEqD-sound (mNat a b c d) (mNat a′ b′ c′ d′) sh-mNat sh-mNat eq with ∧-true₄ eq
... | e1 , e2 , e3 , e4 = cong₄ mNat (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3) (synEq-sound d d′ e4)
synEqD-sound (mEmp a b) (mEmp a′ b′) sh-mEmp sh-mEmp eq with ∧-true eq
... | e1 , e2 = cong₂ mEmp (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (mUnit a b c) (mUnit a′ b′ c′) sh-mUnit sh-mUnit eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ mUnit (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (idt a b c) (idt a′ b′ c′) sh-idt sh-idt eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ idt (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound rfl rfl sh-rfl sh-rfl _ = refl
synEqD-sound (rwt a b c) (rwt a′ b′ c′) sh-rwt sh-rwt eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ rwt (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (def a) (def a′) sh-def sh-def eq = cong def (≡ᵇ-sound eq)
synEqD-sound (ann a b) (ann a′ b′) sh-ann sh-ann eq with ∧-true eq
... | e1 , e2 = cong₂ ann (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (prod a b) (prod a′ b′) sh-prod sh-prod eq with ∧-true eq
... | e1 , e2 = cong₂ prod (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (pair a b) (pair a′ b′) sh-pair sh-pair eq with ∧-true eq
... | e1 , e2 = cong₂ pair (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (fst a) (fst a′) sh-fst sh-fst eq = cong fst (synEq-sound a a′ eq)
synEqD-sound (snd a) (snd a′) sh-snd sh-snd eq = cong snd (synEq-sound a a′ eq)
synEqD-sound (nu a) (nu a′) sh-nu sh-nu eq = cong nu (synEq-sound a a′ eq)
synEqD-sound (unf a b) (unf a′ b′) sh-unf sh-unf eq with ∧-true eq
... | e1 , e2 = cong₂ unf (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (ucons a) (ucons a′) sh-ucons sh-ucons eq = cong ucons (synEq-sound a a′ eq)
synEqD-sound i64 i64 sh-i64 sh-i64 _ = refl
synEqD-sound f32ty f32ty sh-f32ty sh-f32ty _ = refl
synEqD-sound (tensor a b) (tensor a′ b′) sh-tensor sh-tensor eq with ∧-true eq
... | e1 , e2 = cong₂ tensor (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (addi a b) (addi a′ b′) sh-addi sh-addi eq with ∧-true eq
... | e1 , e2 = cong₂ addi (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (muli a b) (muli a′ b′) sh-muli sh-muli eq with ∧-true eq
... | e1 , e2 = cong₂ muli (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (addt a b) (addt a′ b′) sh-addt sh-addt eq with ∧-true eq
... | e1 , e2 = cong₂ addt (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (toi64 a) (toi64 a′) sh-toi64 sh-toi64 eq = cong toi64 (synEq-sound a a′ eq)
synEqD-sound (packi a b) (packi a′ b′) sh-packi sh-packi eq with ∧-true eq
... | e1 , e2 = cong₂ packi (synEq-sound a a′ e1) (synEq-sound b b′ e2)

------------------------------------------------------------------------
-- ≈ is a congruence: it is generated by ⇛, which is.
------------------------------------------------------------------------

≈-map : ∀ {σ m n k} (F : Tm n → Tm k)
  → (∀ {t u} → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] F t ⇛ F u)
  → ∀ {t u} → σ ⊢[ m ] t ≈ u → σ ⊢[ m ] F t ≈ F u
≈-map F h (≈-step s) = ≈-step (h s)
≈-map F h ≈-refl = ≈-refl
≈-map F h (≈-sym c) = ≈-sym (≈-map F h c)
≈-map F h (≈-trans c c′) = ≈-trans (≈-map F h c) (≈-map F h c′)

≈-lam : ∀ {σ m n q} {A A′ : Tm n} {t t′}
  → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] t ≈ t′ → σ ⊢[ m ] lam q A t ≈ lam q A′ t′
≈-lam {q = q} {A′ = A′} {t = t} cA ct =
  ≈-trans (≈-map (λ x → lam q x t) (λ s → ⇛-lam s (⇛-refl _)) cA)
          (≈-map (λ x → lam q A′ x) (λ s → ⇛-lam (⇛-refl _) s) ct)

≈-app : ∀ {σ m n} {f f′ a a′ : Tm n}
  → σ ⊢[ m ] f ≈ f′ → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] app f a ≈ app f′ a′
≈-app {f′ = f′} {a = a} cf ca =
  ≈-trans (≈-map (λ x → app x a) (λ s → ⇛-app s (⇛-refl _)) cf)
          (≈-map (λ x → app f′ x) (λ s → ⇛-app (⇛-refl _) s) ca)

≈-su : ∀ {σ m n} {a a′ : Tm n} → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] su a ≈ su a′
≈-su = ≈-map su ⇛-su

≈-idt : ∀ {σ m n} {A A′ a a′ b b′ : Tm n}
  → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] b ≈ b′
  → σ ⊢[ m ] idt A a b ≈ idt A′ a′ b′
≈-idt {A′ = A′} {a = a} {a′} {b} cA ca cb =
  ≈-trans (≈-map (λ x → idt x a b) (λ s → ⇛-idt s (⇛-refl _) (⇛-refl _)) cA)
  (≈-trans (≈-map (λ x → idt A′ x b) (λ s → ⇛-idt (⇛-refl _) s (⇛-refl _)) ca)
           (≈-map (λ x → idt A′ a′ x) (λ s → ⇛-idt (⇛-refl _) (⇛-refl _) s) cb))

≈-mNat : ∀ {σ m n} {e e′ : Tm n} {P P′ z z′ s s′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] z ≈ z′ → σ ⊢[ m ] s ≈ s′
  → σ ⊢[ m ] mNat e P z s ≈ mNat e′ P′ z′ s′
≈-mNat {e′ = e′} {P} {P′} {z} {z′} {s} ce cP cz cs =
  ≈-trans (≈-map (λ x → mNat x P z s) (λ d → ⇛-mNat d (⇛-refl _) (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → mNat e′ x z s) (λ d → ⇛-mNat (⇛-refl _) d (⇛-refl _) (⇛-refl _)) cP)
  (≈-trans (≈-map (λ x → mNat e′ P′ x s) (λ d → ⇛-mNat (⇛-refl _) (⇛-refl _) d (⇛-refl _)) cz)
           (≈-map (λ x → mNat e′ P′ z′ x) (λ d → ⇛-mNat (⇛-refl _) (⇛-refl _) (⇛-refl _) d) cs)))

≈-mEmp : ∀ {σ m n} {e e′ : Tm n} {P P′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] mEmp e P ≈ mEmp e′ P′
≈-mEmp {e′ = e′} {P} ce cP =
  ≈-trans (≈-map (λ x → mEmp x P) (λ d → ⇛-mEmp d (⇛-refl _)) ce)
          (≈-map (λ x → mEmp e′ x) (λ d → ⇛-mEmp (⇛-refl _) d) cP)

≈-mUnit : ∀ {σ m n} {e e′ : Tm n} {P P′ u u′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] u ≈ u′
  → σ ⊢[ m ] mUnit e P u ≈ mUnit e′ P′ u′
≈-mUnit {e′ = e′} {P} {P′} {u} ce cP cu =
  ≈-trans (≈-map (λ x → mUnit x P u) (λ d → ⇛-mUnit d (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → mUnit e′ x u) (λ d → ⇛-mUnit (⇛-refl _) d (⇛-refl _)) cP)
           (≈-map (λ x → mUnit e′ P′ x) (λ d → ⇛-mUnit (⇛-refl _) (⇛-refl _) d) cu))

≈-rwt : ∀ {σ m n} {e e′ : Tm n} {P P′ t t′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] t ≈ t′
  → σ ⊢[ m ] rwt e P t ≈ rwt e′ P′ t′
≈-rwt {e′ = e′} {P} {P′} {t} ce cP ct =
  ≈-trans (≈-map (λ x → rwt x P t) (λ d → ⇛-rwt d (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → rwt e′ x t) (λ d → ⇛-rwt (⇛-refl _) d (⇛-refl _)) cP)
           (≈-map (λ x → rwt e′ P′ x) (λ d → ⇛-rwt (⇛-refl _) (⇛-refl _) d) ct))

≈-ann : ∀ {σ m n} {e e′ A A′ : Tm n}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] ann e A ≈ ann e′ A′
≈-ann {e′ = e′} {A} ce cA =
  ≈-trans (≈-map (λ x → ann x A) (λ d → ⇛-annc d (⇛-refl _)) ce)
          (≈-map (λ x → ann e′ x) (λ d → ⇛-annc (⇛-refl _) d) cA)

⇛L-++ˡ : ∀ {σ m n} (pre : List (Tm n)) {xs ys}
  → σ ⊢[ m ] xs ⇛L ys → σ ⊢[ m ] pre ++ xs ⇛L pre ++ ys
⇛L-++ˡ [] d = d
⇛L-++ˡ (p ∷ pre) d = ⇛L-∷ (⇛-refl p) (⇛L-++ˡ pre d)

≈-mData-bs : ∀ {σ m n} {e : Tm n} {P} (pre : List (Tm n)) {bs bs′}
  → σ ⊢[ m ] bs ≈L bs′ → σ ⊢[ m ] mData e P (pre ++ bs) ≈ mData e P (pre ++ bs′)
≈-mData-bs pre ≈L-[] = ≈-refl
≈-mData-bs {σ} {m} {e = e} {P} pre (≈L-∷ {a} {b} {as} {bs} c cs) =
  ≈-trans
    (≈-map (λ x → mData e P (pre ++ x ∷ as))
           (λ d → ⇛-mData (⇛-refl _) (⇛-refl _) (⇛L-++ˡ pre (⇛L-∷ d (⇛L-refl as)))) c)
    (subst₂ (λ xs ys → σ ⊢[ m ] mData e P xs ≈ mData e P ys)
            (++-assoc pre (b ∷ []) as) (++-assoc pre (b ∷ []) bs)
            (≈-mData-bs (pre ++ b ∷ []) cs))

≈-mData : ∀ {σ m n} {e e′ : Tm n} {P P′ bs bs′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] bs ≈L bs′
  → σ ⊢[ m ] mData e P bs ≈ mData e′ P′ bs′
≈-mData {e′ = e′} {P} {P′} {bs} ce cP cbs =
  ≈-trans (≈-map (λ x → mData x P bs) (λ d → ⇛-mData d (⇛-refl _) (⇛L-refl _)) ce)
  (≈-trans (≈-map (λ x → mData e′ x bs) (λ d → ⇛-mData (⇛-refl _) d (⇛L-refl _)) cP)
           (≈-mData-bs [] cbs))

------------------------------------------------------------------------
-- conv decides ≈ (soundly). Fuel only bounds the search.
------------------------------------------------------------------------

fail≢ok : ∀ {A : Set} {e} {x : A} → fail e ≡ ok x → ⊥
fail≢ok ()

conv-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v
convArgs-sound : ∀ k σ {n} {us vs : List (Tm n)} → FragSig σ → FragL us → FragL vs
  → convArgs k σ us vs ≡ ok tt → σ ⊢[ spec ] us ≈L vs
convStuck-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → ∀ du dv → defArgs u ≡ du → defArgs v ≡ dv
  → convStuck k σ u v du dv ≡ ok tt → σ ⊢[ spec ] u ≈ v
convN-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → convN k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v
convND-sound : ∀ k σ {n} {t} {u v : Tm n} → TmShape t u → TmShape t v
  → FragSig σ → Frag u → Frag v
  → convND k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v

conv-sound (suc k) σ {u = u} {v} fs Fu Fv eq with synEq u v in seq
... | true with synEq-sound u v seq
...   | refl = ≈-refl
conv-sound (suc k) σ fs Fu Fv eq | false = convStuck-sound k σ fs Fu Fv _ _ refl refl eq

convArgs-sound k σ fs fl-[] fl-[] _ = ≈L-[]
convArgs-sound k σ fs (fl-∷ Fa Fas) (fl-∷ Fb Fbs) eq with >>-ok eq
... | (_ , ca) , cas = ≈L-∷ (conv-sound k σ fs Fa Fb ca) (convArgs-sound k σ fs Fas Fbs cas)

-- The fallback: whnf both sides and compare.
convWhnf-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → convN k σ (whnf k σ u) (whnf k σ v) ≡ ok tt → σ ⊢[ spec ] u ≈ v
convWhnf-sound k σ fs Fu Fv eq =
  ≈-trans (whnf-≈ k σ fs Fu)
  (≈-trans (convN-sound k σ fs (whnf-Frag k σ fs Fu) (whnf-Frag k σ fs Fv) eq)
           (≈-sym (whnf-≈ k σ fs Fv)))

convStuck-sound k σ {u = u} {v} fs Fu Fv (just (i , a , as)) (just (j , b , bs)) du dv eq
  with (i ≡ᵇ j) ∧ not (ctorHead a) ∧ not (ctorHead b) in ceq
... | false = convWhnf-sound k σ fs Fu Fv eq
... | true with ≡ᵇ-sound {i} {j} (proj₁ (∧-true {i ≡ᵇ j} ceq)) | defArgs-just du | defArgs-just dv | >>-ok eq
...   | refl | spu | spv | (_ , ca) , cas with Frag-Spine spu Fu | Frag-Spine spv Fv
...     | _ , fl-∷ Fa Fas | _ , fl-∷ Fb Fbs =
  subst₂ (λ x y → σ ⊢[ spec ] x ≈ y) (sym (Spine-≡ spu)) (sym (Spine-≡ spv))
    (≈-appsFrom {f = def i} ≈-refl
      (≈L-∷ (conv-sound k σ fs Fa Fb ca) (convArgs-sound k σ fs Fas Fbs cas)))
convStuck-sound k σ fs Fu Fv (just _) nothing _ _ eq = convWhnf-sound k σ fs Fu Fv eq
convStuck-sound k σ fs Fu Fv nothing _ _ _ eq = convWhnf-sound k σ fs Fu Fv eq

convN-sound k σ {u = u} {v} fs Fu Fv eq with tmTag u ≡ᵇ tmTag v in teq
... | true = convND-sound k σ (shape u) (subst (λ x → TmShape x v) (sym (≡ᵇ-sound teq)) (shape v)) fs Fu Fv eq
... | false = ⊥-elim (fail≢ok eq)

convND-sound k σ (sh-var {x}) (sh-var {y}) fs _ _ eq with eqFin-sound x y (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ sh-typ sh-typ fs _ _ _ = ≈-refl
convND-sound k σ (sh-pi {q}) (sh-pi {q′}) fs (f-pi FA FB) (f-pi FA′ FB′) eq with >>-ok₂ eq
... | (_ , g) , (_ , cA) , cB with eqQty-sound q q′ (guard-ok g)
...   | refl = ≈-pi (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs FB FB′ cB)
convND-sound k σ (sh-lam {q}) (sh-lam {q′}) fs (f-lam FA Ft) (f-lam FA′ Ft′) eq with >>-ok₂ eq
... | (_ , g) , (_ , cA) , ct with eqQty-sound q q′ (guard-ok g)
...   | refl = ≈-lam (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs Ft Ft′ ct)
convND-sound k σ sh-app sh-app fs (f-app Ff Fa) (f-app Fg Fb) eq with >>-ok eq
... | (_ , cf) , ca = ≈-app (conv-sound k σ fs Ff Fg cf) (conv-sound k σ fs Fa Fb ca)
convND-sound k σ sh-nat sh-nat fs _ _ _ = ≈-refl
convND-sound k σ sh-ze sh-ze fs _ _ _ = ≈-refl
convND-sound k σ sh-su sh-su fs (f-su Fa) (f-su Fb) eq = ≈-su (conv-sound k σ fs Fa Fb eq)
convND-sound k σ sh-unit sh-unit fs _ _ _ = ≈-refl
convND-sound k σ sh-one sh-one fs _ _ _ = ≈-refl
convND-sound k σ sh-empty sh-empty fs _ _ _ = ≈-refl
convND-sound k σ (sh-dty {i}) (sh-dty {j}) fs _ _ eq with ≡ᵇ-sound {i} {j} (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ (sh-ctor {i} {j}) (sh-ctor {i′} {j′}) fs _ _ eq with ∧-true (guard-ok eq)
... | ei , ej with ≡ᵇ-sound {i} {i′} ei | ≡ᵇ-sound {j} {j′} ej
...   | refl | refl = ≈-refl
convND-sound k σ sh-mData sh-mData fs (f-mData Fe FP Fbs) (f-mData Fe′ FP′ Fbs′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , cbs =
  ≈-mData (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (convArgs-sound k σ fs Fbs Fbs′ cbs)
convND-sound k σ sh-mNat sh-mNat fs (f-mNat Fe FP Fz Fs) (f-mNat Fe′ FP′ Fz′ Fs′) eq with >>-ok₃ eq
... | (_ , ce) , (_ , cP) , (_ , cz) , cs =
  ≈-mNat (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP)
         (conv-sound k σ fs Fz Fz′ cz) (conv-sound k σ fs Fs Fs′ cs)
convND-sound k σ sh-mEmp sh-mEmp fs (f-mEmp Fe FP) (f-mEmp Fe′ FP′) eq with >>-ok eq
... | (_ , ce) , cP = ≈-mEmp (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP)
convND-sound k σ sh-mUnit sh-mUnit fs (f-mUnit Fe FP Fu) (f-mUnit Fe′ FP′ Fu′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , cu =
  ≈-mUnit (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (conv-sound k σ fs Fu Fu′ cu)
convND-sound k σ sh-idt sh-idt fs (f-idt FA Fa Fb) (f-idt FA′ Fa′ Fb′) eq with >>-ok₂ eq
... | (_ , cA) , (_ , ca) , cb =
  ≈-idt (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs Fa Fa′ ca) (conv-sound k σ fs Fb Fb′ cb)
convND-sound k σ sh-rfl sh-rfl fs _ _ _ = ≈-refl
convND-sound k σ sh-rwt sh-rwt fs (f-rwt Fe FP Ft) (f-rwt Fe′ FP′ Ft′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , ct =
  ≈-rwt (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (conv-sound k σ fs Ft Ft′ ct)
convND-sound k σ (sh-def {i}) (sh-def {j}) fs _ _ eq with ≡ᵇ-sound {i} {j} (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ sh-ann sh-ann fs (f-ann Fe FA) (f-ann Fe′ FA′) eq with >>-ok eq
... | (_ , ce) , cA = ≈-ann (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FA FA′ cA)
convND-sound k σ sh-prod sh-prod fs () _ _
convND-sound k σ sh-pair sh-pair fs () _ _
convND-sound k σ sh-fst sh-fst fs () _ _
convND-sound k σ sh-snd sh-snd fs () _ _
convND-sound k σ sh-nu sh-nu fs () _ _
convND-sound k σ sh-unf sh-unf fs () _ _
convND-sound k σ sh-ucons sh-ucons fs () _ _
convND-sound k σ sh-i64 sh-i64 fs () _ _
convND-sound k σ sh-f32ty sh-f32ty fs () _ _
convND-sound k σ sh-tensor sh-tensor fs () _ _
convND-sound k σ sh-addi sh-addi fs () _ _
convND-sound k σ sh-muli sh-muli fs () _ _
convND-sound k σ sh-addt sh-addt fs () _ _
convND-sound k σ sh-toi64 sh-toi64 fs () _ _
convND-sound k σ sh-packi sh-packi fs () _ _

------------------------------------------------------------------------
-- Part 2: the checker's views of a type.
------------------------------------------------------------------------

>>=-ok : ∀ {A B : Set} {r : Result A} {f : A → Result B} {x}
  → (r >>= f) ≡ ok x → ∃ λ y → (r ≡ ok y) × (f y ≡ ok x)
>>=-ok {r = ok y} eq = y , refl , eq

if-ok : ∀ {b s} {y : ⊤} → (if b then ok tt else fail s) ≡ ok y → b ≡ true
if-ok {true} _ = refl

whnf-pi : ∀ k σ {n q} {A : Tm n} {B} → whnf k σ (pi q A B) ≡ pi q A B
whnf-pi zero σ = refl
whnf-pi (suc k) σ = refl

-- dty spines are whnf-normal for whnf.
whnf-dty : ∀ k σ {n i} {as : List (Tm n)} {e} → Spine (dty i) as e → whnf k σ e ≡ e
whnf-dty zero σ sp = refl
whnf-dty (suc k) σ sp-[] = refl
whnf-dty (suc k) σ (sp-snoc {f = f} sp) with whnf k σ f | whnf-dty k σ sp
whnf-dty (suc k) σ (sp-snoc sp-[]) | _ | refl = refl
whnf-dty (suc k) σ (sp-snoc (sp-snoc _)) | _ | refl = refl

viewPi-sound : ∀ k σ {n} {T : Tm n} {q A B}
  → viewPi k σ T ≡ ok (q , A , B) → whnf k σ T ≡ pi q A B
viewPi-sound k σ {T = T} eq with whnf k σ T
viewPi-sound k σ refl | pi _ _ _ = refl
viewPi-sound k σ () | (var _)
viewPi-sound k σ () | typ
viewPi-sound k σ () | (lam _ _ _)
viewPi-sound k σ () | (app _ _)
viewPi-sound k σ () | nat
viewPi-sound k σ () | ze
viewPi-sound k σ () | (su _)
viewPi-sound k σ () | unit
viewPi-sound k σ () | one
viewPi-sound k σ () | empty
viewPi-sound k σ () | (dty _)
viewPi-sound k σ () | (ctor _ _)
viewPi-sound k σ () | (mData _ _ _)
viewPi-sound k σ () | (mNat _ _ _ _)
viewPi-sound k σ () | (mEmp _ _)
viewPi-sound k σ () | (mUnit _ _ _)
viewPi-sound k σ () | (idt _ _ _)
viewPi-sound k σ () | rfl
viewPi-sound k σ () | (rwt _ _ _)
viewPi-sound k σ () | (def _)
viewPi-sound k σ () | (ann _ _)
viewPi-sound k σ () | (prod _ _)
viewPi-sound k σ () | (pair _ _)
viewPi-sound k σ () | (fst _)
viewPi-sound k σ () | (snd _)
viewPi-sound k σ () | (nu _)
viewPi-sound k σ () | (unf _ _)
viewPi-sound k σ () | (ucons _)
viewPi-sound k σ () | i64
viewPi-sound k σ () | f32ty
viewPi-sound k σ () | (tensor _ _)
viewPi-sound k σ () | (addi _ _)
viewPi-sound k σ () | (muli _ _)
viewPi-sound k σ () | (addt _ _)
viewPi-sound k σ () | (toi64 _)
viewPi-sound k σ () | (packi _ _)

viewId-sound : ∀ k σ {n} {T : Tm n} {A a b}
  → viewId k σ T ≡ ok (A , a , b) → whnf k σ T ≡ idt A a b
viewId-sound k σ {T = T} eq with whnf k σ T
viewId-sound k σ refl | idt _ _ _ = refl
viewId-sound k σ () | (var _)
viewId-sound k σ () | typ
viewId-sound k σ () | (pi _ _ _)
viewId-sound k σ () | (lam _ _ _)
viewId-sound k σ () | (app _ _)
viewId-sound k σ () | nat
viewId-sound k σ () | ze
viewId-sound k σ () | (su _)
viewId-sound k σ () | unit
viewId-sound k σ () | one
viewId-sound k σ () | empty
viewId-sound k σ () | (dty _)
viewId-sound k σ () | (ctor _ _)
viewId-sound k σ () | (mData _ _ _)
viewId-sound k σ () | (mNat _ _ _ _)
viewId-sound k σ () | (mEmp _ _)
viewId-sound k σ () | (mUnit _ _ _)
viewId-sound k σ () | rfl
viewId-sound k σ () | (rwt _ _ _)
viewId-sound k σ () | (def _)
viewId-sound k σ () | (ann _ _)
viewId-sound k σ () | (prod _ _)
viewId-sound k σ () | (pair _ _)
viewId-sound k σ () | (fst _)
viewId-sound k σ () | (snd _)
viewId-sound k σ () | (nu _)
viewId-sound k σ () | (unf _ _)
viewId-sound k σ () | (ucons _)
viewId-sound k σ () | i64
viewId-sound k σ () | f32ty
viewId-sound k σ () | (tensor _ _)
viewId-sound k σ () | (addi _ _)
viewId-sound k σ () | (muli _ _)
viewId-sound k σ () | (addt _ _)
viewId-sound k σ () | (toi64 _)
viewId-sound k σ () | (packi _ _)

viewData-sound : ∀ k σ {n} {T : Tm n} {di ps idxs}
  → viewData k σ T ≡ ok (di , ps , idxs)
  → ∃ λ d → ∃ λ args
    → (lookupData σ di ≡ ok d) × Spine (dty di) args (whnf k σ T)
    × (length args ≡ nparams d + nidxs d)
    × (ps ≡ take (nparams d) args) × (idxs ≡ drop (nparams d) args)
viewData-sound k σ {T = T} {di} {ps} {idxs} eq with dtyArgs (whnf k σ T) in deq
... | nothing = ⊥-elim (fail≢ok eq)
... | just (i , args) with lookupData σ i in leq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok d with length args ≡ᵇ (nparams d + nidxs d) in geq
...     | false = ⊥-elim (fail≢ok eq)
...     | true with ok-inj eq
...       | refl = d , args , leq , dtyArgs-just deq , ≡ᵇ-sound geq , refl , refl

------------------------------------------------------------------------
-- isData decides IsData (soundly).
------------------------------------------------------------------------

FragL-take : ∀ {n} k {as : List (Tm n)} → FragL as → FragL (take k as)
FragL-take zero _ = fl-[]
FragL-take (suc k) fl-[] = fl-[]
FragL-take (suc k) (fl-∷ F Fs) = fl-∷ F (FragL-take k Fs)

FragL-drop : ∀ {n} k {as : List (Tm n)} → FragL as → FragL (drop k as)
FragL-drop zero Fs = Fs
FragL-drop (suc k) fl-[] = fl-[]
FragL-drop (suc k) (fl-∷ F Fs) = FragL-drop k Fs

isData-sound : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → isData k σ t ≡ true → IsData σ t
allData-sound : ∀ k σ {n} {ts : List (Tm n)} → FragSig σ → FragL ts
  → allData k σ ts ≡ true → AllData σ ts

allData-sound k σ fs fl-[] _ = ad-[]
allData-sound k σ fs (fl-∷ F Fs) eq with ∧-true eq
... | e , es = ad-∷ (isData-sound k σ fs F e) (allData-sound k σ fs Fs es)

isData-sound (suc k) σ {t = t} fs Ft eq
  with unspine (whnf (suc k) σ t) in ueq | whnf-sound (suc k) σ fs Ft
... | (nat , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = d-conv (⟶*→≈ r) (subst (IsData σ) (sym weq) d-nat)
isData-sound (suc k) σ fs Ft eq | (unit , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = d-conv (⟶*→≈ r) (subst (IsData σ) (sym weq) d-unit)
isData-sound (suc k) σ fs Ft eq | (empty , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = d-conv (⟶*→≈ r) (subst (IsData σ) (sym weq) d-empty)
isData-sound (suc k) σ fs Ft eq | (i64 , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq F))
  where noFrag : ∀ {n} → Frag {n} i64 → ⊥
        noFrag ()
isData-sound (suc k) σ fs Ft eq | (f32ty , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq F))
  where noFrag : ∀ {n} → Frag {n} f32ty → ⊥
        noFrag ()
isData-sound (suc k) σ fs Ft eq | (tensor _ _ , []) | r , F with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq F))
  where noFrag : ∀ {n d s} → Frag {n} (tensor d s) → ⊥
        noFrag ()
isData-sound (suc k) σ {t = t} fs Ft eq | (dty i , as) | r , F with lookupData σ i in leq
...   | fail _ = ⊥-elim (false≢true eq)
  where false≢true : false ≡ true → ⊥
        false≢true ()
...   | ok d with unspine→Spine′ ueq
...     | sp = d-conv (⟶*→≈ r)
      (d-dty leq sp (allData-sound k σ fs (FragL-take (nparams d) (proj₂ (Frag-Spine sp F))) eq))
isData-sound (suc k) σ fs Ft () | ((var _) , _) | _
isData-sound (suc k) σ fs Ft () | (typ , _) | _
isData-sound (suc k) σ fs Ft () | ((pi _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((lam _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((app _ _) , _) | _
isData-sound (suc k) σ fs Ft () | (nat , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | (ze , _) | _
isData-sound (suc k) σ fs Ft () | ((su _) , _) | _
isData-sound (suc k) σ fs Ft () | (unit , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | (one , _) | _
isData-sound (suc k) σ fs Ft () | (empty , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | ((ctor _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((mData _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((mNat _ _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((mEmp _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((mUnit _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((idt _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | (rfl , _) | _
isData-sound (suc k) σ fs Ft () | ((rwt _ _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((def _) , _) | _
isData-sound (suc k) σ fs Ft () | ((ann _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((prod _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((pair _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((fst _) , _) | _
isData-sound (suc k) σ fs Ft () | ((snd _) , _) | _
isData-sound (suc k) σ fs Ft () | ((nu _) , _) | _
isData-sound (suc k) σ fs Ft () | ((unf _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((ucons _) , _) | _
isData-sound (suc k) σ fs Ft () | (i64 , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | (f32ty , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | ((tensor _ _) , _ ∷ _) | _
isData-sound (suc k) σ fs Ft () | ((addi _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((muli _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((addt _ _) , _) | _
isData-sound (suc k) σ fs Ft () | ((toi64 _) , _) | _
isData-sound (suc k) σ fs Ft () | ((packi _ _) , _) | _
