------------------------------------------------------------------------
-- Soundness of the executable checker with respect to ⊢, on the ⊢
-- fragment (Muro.Frag): when Muro.Check says yes, ⊢ has a derivation.
--
-- Part 1: weak-head normalisation and conversion.
--   whnf-sound   whnf k σ t is reached from t by ⟶ (spec), and stays in
--                the fragment;
--   synEq-sound  synEq u v ≡ true → u ≡ v;
--   conv-sound   conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v.
-- Part 2: the views (viewPi, viewId, viewData, lamView) and isData.
-- Part 3: what the proof assumes of the signature (GoodSig: fragment,
--   non-indexed data, constructor types are telescopes ending in the
--   data type), instParams and analyzeForces on such a telescope.
-- Part 4: infer-sound / check-sound / checkTy-sound, by structural
--   recursion on a depth-indexed copy of the fragment (FragD).
-- Part 5: the same over plain Frag, and checkDef-sound / checkSig-sound:
--   every definition Check accepts is derivable in ⊢.
--
-- One direction only: nothing here says ⊢ derivations are found by
-- Check. Fuel is universally quantified.
--
-- This module imports Muro.Check, which carries TERMINATING pragmas, so
-- it cannot be --safe. Everything it relies on from the theory side
-- (Convert, Reduction, Frag, Spine, Tag, Data, Judgement) is --safe.
------------------------------------------------------------------------

module Muro.Soundness where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_; _⊓_; _∸_; _⊔_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
import Data.Vec.Base as Vec
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
         isData; allData; dataParamsData; instParams; isRunType;
         infer; check; checkTy; checkAgainst; checkCtorArgs; checkCtorApp; checkBr;
         checkBranches; checkMotive; firstMotLam; nparamsOf; analyzeForces; forcePairs;
         forcesFor; countPis; wkForces; lookupForce; matchIdxs; RecSt; extRec; keepNext;
         scrutOk; checkRec; floatIdForbidden; isDType;
         checkDef; checkDefs; checkDatas; checkSig; emptyRec; defRec)
open import Muro.Judgement
open import Muro.Wall using (spec-⇒-uses)
open import Muro.Typing using (typ-ext-suc; ≈-≡)
open import Data.List.Properties using (take++drop≡id; length-take; length-drop)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m; m≤m+n; m+n∸m≡n; +-identityʳ; +-suc; m≤m⊔n; m≤n⊔m; n≤1+n)

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

------------------------------------------------------------------------
-- Part 3: the signatures covered, and the shape of constructor types.
------------------------------------------------------------------------

-- A constructor type: Π-binders, then the data type applied to exactly
-- np arguments (Check.checkTelPos with no indices).
data Tel (i np : ℕ) : ∀ {n} → Tm n → Set where
  tel-pi  : ∀ {n q} {A : Tm n} {B} → Tel i np B → Tel i np (pi q A B)
  tel-end : ∀ {n} {as : List (Tm n)} {e} → Spine (dty i) as e → length as ≡ np → Tel i np e

Tel-ren : ∀ {i np n k} (ρ : Fin n → Fin k) {T : Tm n} → Tel i np T → Tel i np (ren ρ T)
Tel-ren ρ (tel-pi tl) = tel-pi (Tel-ren (lift ρ) tl)
Tel-ren ρ (tel-end {as = as} sp len) =
  tel-end (Spine-ren ρ sp) (trans (renList-length ρ as) len)

Tel-sub : ∀ {i np n k} (τ : Fin n → Tm k) {T : Tm n} → Tel i np T → Tel i np (sub τ T)
Tel-sub τ (tel-pi tl) = tel-pi (Tel-sub (lifts τ) tl)
Tel-sub τ (tel-end {as = as} sp len) =
  tel-end (Spine-sub τ sp) (trans (subList-length τ as) len)

Tel-whnf : ∀ k σ {i np n} {T : Tm n} → Tel i np T → whnf k σ T ≡ T
Tel-whnf k σ (tel-pi _) = whnf-pi k σ
Tel-whnf k σ (tel-end sp _) = whnf-dty k σ sp

-- Signatures the soundness theorem covers: in the fragment, data types
-- without indices, constructor types telescopes into their data type.
record GoodSig (σ : Sig) : Set where
  field
    frag   : FragSig σ
    nonIdx : ∀ i d → lookupData σ i ≡ ok d → DataDecl.idxs d ≡ []
    tel    : ∀ i d → lookupData σ i ≡ ok d → ∀ j c → lookupCtor d j ≡ ok c
             → Tel i (nparams d) (Ctor.ctype c)

-- The constructors still to be matched, with what is known of them.
data CtorsOk (i np : ℕ) : List Ctor → Set where
  co-[] : CtorsOk i np []
  co-∷  : ∀ {c cs} → Frag (Ctor.ctype c) → Tel i np (Ctor.ctype c)
    → CtorsOk i np cs → CtorsOk i np (c ∷ cs)

ctorsOk-go : ∀ {i np} (cs : List Ctor)
  → (∀ j c → lookupList cs j ≡ ok c → Frag (Ctor.ctype c) × Tel i np (Ctor.ctype c))
  → CtorsOk i np cs
ctorsOk-go [] h = co-[]
ctorsOk-go (c ∷ cs) h with h 0 c refl
... | F , tl = co-∷ F tl (ctorsOk-go cs (λ j c′ e → h (suc j) c′ e))

ctorsOk : ∀ {σ i d} → GoodSig σ → lookupData σ i ≡ ok d
  → CtorsOk i (nparams d) (DataDecl.ctors d)
ctorsOk {σ} {i} {d} G leq =
  ctorsOk-go (DataDecl.ctors d)
    (λ j c e → FragCtors-lookup (proj₂ (FragSig.datas (GoodSig.frag G) i d leq)) e
             , GoodSig.tel G i d leq j c e)

------------------------------------------------------------------------
-- instParams, and the forces of a non-indexed telescope.
------------------------------------------------------------------------

instParams-sound : ∀ k σ {n} {T : Tm n} {ps R i np} → FragSig σ → Frag T → FragL ps
  → Tel i np T → instParams k σ T ps ≡ ok R
  → InstParams σ T ps R × Frag R × Tel i np R
instParams-sound k σ fs FT fl-[] tl refl = ip-[] , FT , tl
instParams-sound k σ {T = T} fs FT (fl-∷ Fp Fps) tl eq rewrite Tel-whnf k σ tl with tl
... | tel-end sp-[] _ = ⊥-elim (fail≢ok eq)
... | tel-end (sp-snoc _) _ = ⊥-elim (fail≢ok eq)
instParams-sound k σ fs (f-pi FA FB) (fl-∷ Fp Fps) _ eq | tel-pi tl
  with instParams-sound k σ fs (Frag-inst FB Fp) Fps (Tel-sub _ tl) eq
... | ip , FR , tlR = ip-∷ ≈-refl ip , FR , tlR

drop-all : ∀ {A : Set} n (xs : List A) → length xs ≡ n → drop n xs ≡ []
drop-all zero [] _ = refl
drop-all (suc n) (x ∷ xs) eq = drop-all n xs (cong pred eq)
  where pred : ℕ → ℕ
        pred zero = zero
        pred (suc n) = n

nparamsOf-ok : ∀ {σ i d} → lookupData σ i ≡ ok d → nparamsOf σ i ≡ nparams d
nparamsOf-ok {σ} {i} eq with lookupData σ i
nparamsOf-ok refl | ok d = refl

-- Forces of a non-indexed telescope: one `nothing` per binder.
noForces : ∀ {n m} → Tm m → List (Maybe (Tm n))
noForces T = forcesFor (countPis T) []

forcePairs-tel : ∀ k σ {n m} {np i d} {T : Tm m} → Tel i np T
  → forcePairs {n} k σ np [] d T ≡ ok []
forcePairs-tel k σ (tel-pi tl) = forcePairs-tel k σ tl
forcePairs-tel k σ {m = m} {np = np} {i = i} (tel-end {as = as} sp-[] len)
  rewrite whnf-dty k σ {m} {i} (sp-[] {h = dty i}) | drop-all np as len = refl
forcePairs-tel k σ {np = np} (tel-end {as = as} (sp-snoc {a = a} sp) len)
  rewrite whnf-dty k σ (sp-snoc {a = a} sp) | Spine→unspine head-dty (sp-snoc {a = a} sp)
        | drop-all np as len = refl

analyzeForces-tel : ∀ k σ {n np i} {T : Tm n} → Tel i np T
  → analyzeForces k σ np [] T ≡ ok (noForces T)
analyzeForces-tel k σ {n = n} tl rewrite forcePairs-tel k σ {n = n} {d = 0} tl = refl

wkForces-noForces : ∀ {n} c → wkForces {n} (forcesFor c []) ≡ forcesFor c []
wkForces-noForces zero = refl
wkForces-noForces (suc c) = cong (nothing ∷_) (wkForces-noForces c)

FragCtx-ext : ∀ {n} {Γ : Ctx n} {q A} → FragCtx Γ → Frag A → FragCtx (ext Γ q A)
FragCtx-ext FΓ FA zero = Frag-wk FA
FragCtx-ext {Γ = Γ} {q} {A} FΓ FA (suc x) rewrite typ-ext-suc Γ q A x = Frag-wk (FΓ x)

-- A branch applied to the motive: Check writes the motive as a λ.
β-mot : ∀ {σ n q} {D : Tm n} {P e} → σ ⊢[ spec ] app (lam q D P) e ≈ inst P e
β-mot = ≈-step (⇛-β (⇛-refl _) (⇛-refl _))

------------------------------------------------------------------------
-- The fragment with an explicit depth. The soundness proof recurses on
-- the depth: a constructor spine is taken apart by a function
-- (FragD-Spine), which the termination checker cannot follow, but the
-- depth it hands back is smaller. Depths are positive (a leaf is at
-- suc d, a node one above its children, a non-empty list at the depth
-- of its elements), so every function of the proof takes FragD (suc d)
-- and matching a node refines d to suc d′ without a zero case.
------------------------------------------------------------------------

data FragD {n} : ℕ → Tm n → Set
data FragDL {n} : ℕ → List (Tm n) → Set

data FragD {n} where
  fd-var   : ∀ {d x} → FragD (suc d) (var x)
  fd-typ   : ∀ {d} → FragD (suc d) typ
  fd-pi    : ∀ {d q A B} → FragD (suc d) A → FragD (suc d) B → FragD (suc (suc d)) (pi q A B)
  fd-lam   : ∀ {d q A t} → FragD (suc d) A → FragD (suc d) t → FragD (suc (suc d)) (lam q A t)
  fd-app   : ∀ {d f a} → FragD (suc d) f → FragD (suc d) a → FragD (suc (suc d)) (app f a)
  fd-nat   : ∀ {d} → FragD (suc d) nat
  fd-ze    : ∀ {d} → FragD (suc d) ze
  fd-su    : ∀ {d t} → FragD (suc d) t → FragD (suc (suc d)) (su t)
  fd-unit  : ∀ {d} → FragD (suc d) unit
  fd-one   : ∀ {d} → FragD (suc d) one
  fd-empty : ∀ {d} → FragD (suc d) empty
  fd-dty   : ∀ {d i} → FragD (suc d) (dty i)
  fd-ctor  : ∀ {d i j} → FragD (suc d) (ctor i j)
  fd-mData : ∀ {d e P bs} → FragD (suc d) e → FragD (suc d) P → FragDL (suc d) bs → FragD (suc (suc d)) (mData e P bs)
  fd-mNat  : ∀ {d e P z s} → FragD (suc d) e → FragD (suc d) P → FragD (suc d) z → FragD (suc d) s → FragD (suc (suc d)) (mNat e P z s)
  fd-mEmp  : ∀ {d e P} → FragD (suc d) e → FragD (suc d) P → FragD (suc (suc d)) (mEmp e P)
  fd-mUnit : ∀ {d e P u} → FragD (suc d) e → FragD (suc d) P → FragD (suc d) u → FragD (suc (suc d)) (mUnit e P u)
  fd-idt   : ∀ {d A a b} → FragD (suc d) A → FragD (suc d) a → FragD (suc d) b → FragD (suc (suc d)) (idt A a b)
  fd-rfl   : ∀ {d} → FragD (suc d) rfl
  fd-rwt   : ∀ {d e P t} → FragD (suc d) e → FragD (suc d) P → FragD (suc d) t → FragD (suc (suc d)) (rwt e P t)
  fd-def   : ∀ {d i} → FragD (suc d) (def i)
  fd-ann   : ∀ {d e A} → FragD (suc d) e → FragD (suc d) A → FragD (suc (suc d)) (ann e A)

data FragDL {n} where
  fdl-[] : ∀ {d} → FragDL d []
  fdl-∷  : ∀ {d t ts} → FragD (suc d) t → FragDL (suc d) ts → FragDL (suc d) (t ∷ ts)

FragD→Frag : ∀ {n d} {t : Tm n} → FragD d t → Frag t
FragDL→FragL : ∀ {n d} {ts : List (Tm n)} → FragDL d ts → FragL ts
FragD→Frag fd-var = f-var
FragD→Frag fd-typ = f-typ
FragD→Frag (fd-pi A B) = f-pi (FragD→Frag A) (FragD→Frag B)
FragD→Frag (fd-lam A t) = f-lam (FragD→Frag A) (FragD→Frag t)
FragD→Frag (fd-app f a) = f-app (FragD→Frag f) (FragD→Frag a)
FragD→Frag fd-nat = f-nat
FragD→Frag fd-ze = f-ze
FragD→Frag (fd-su t) = f-su (FragD→Frag t)
FragD→Frag fd-unit = f-unit
FragD→Frag fd-one = f-one
FragD→Frag fd-empty = f-empty
FragD→Frag fd-dty = f-dty
FragD→Frag fd-ctor = f-ctor
FragD→Frag (fd-mData e P bs) = f-mData (FragD→Frag e) (FragD→Frag P) (FragDL→FragL bs)
FragD→Frag (fd-mNat e P z s) = f-mNat (FragD→Frag e) (FragD→Frag P) (FragD→Frag z) (FragD→Frag s)
FragD→Frag (fd-mEmp e P) = f-mEmp (FragD→Frag e) (FragD→Frag P)
FragD→Frag (fd-mUnit e P u) = f-mUnit (FragD→Frag e) (FragD→Frag P) (FragD→Frag u)
FragD→Frag (fd-idt A a b) = f-idt (FragD→Frag A) (FragD→Frag a) (FragD→Frag b)
FragD→Frag fd-rfl = f-rfl
FragD→Frag (fd-rwt e P t) = f-rwt (FragD→Frag e) (FragD→Frag P) (FragD→Frag t)
FragD→Frag fd-def = f-def
FragD→Frag (fd-ann e A) = f-ann (FragD→Frag e) (FragD→Frag A)
FragDL→FragL fdl-[] = fl-[]
FragDL→FragL (fdl-∷ t ts) = fl-∷ (FragD→Frag t) (FragDL→FragL ts)

-- depth is an upper bound
FragD-mono : ∀ {n d d′} {t : Tm n} → d ≤ d′ → FragD d t → FragD d′ t
FragDL-mono : ∀ {n d d′} {ts : List (Tm n)} → d ≤ d′ → FragDL d ts → FragDL d′ ts
FragD-mono (s≤s le) fd-var = fd-var
FragD-mono (s≤s le) fd-typ = fd-typ
FragD-mono (s≤s (s≤s le)) (fd-pi A B) = fd-pi (FragD-mono (s≤s le) A) (FragD-mono (s≤s le) B)
FragD-mono (s≤s (s≤s le)) (fd-lam A t) = fd-lam (FragD-mono (s≤s le) A) (FragD-mono (s≤s le) t)
FragD-mono (s≤s (s≤s le)) (fd-app f a) = fd-app (FragD-mono (s≤s le) f) (FragD-mono (s≤s le) a)
FragD-mono (s≤s le) fd-nat = fd-nat
FragD-mono (s≤s le) fd-ze = fd-ze
FragD-mono (s≤s (s≤s le)) (fd-su t) = fd-su (FragD-mono (s≤s le) t)
FragD-mono (s≤s le) fd-unit = fd-unit
FragD-mono (s≤s le) fd-one = fd-one
FragD-mono (s≤s le) fd-empty = fd-empty
FragD-mono (s≤s le) fd-dty = fd-dty
FragD-mono (s≤s le) fd-ctor = fd-ctor
FragD-mono (s≤s (s≤s le)) (fd-mData e P bs) = fd-mData (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) P) (FragDL-mono (s≤s le) bs)
FragD-mono (s≤s (s≤s le)) (fd-mNat e P z s) =
  fd-mNat (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) P) (FragD-mono (s≤s le) z) (FragD-mono (s≤s le) s)
FragD-mono (s≤s (s≤s le)) (fd-mEmp e P) = fd-mEmp (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) P)
FragD-mono (s≤s (s≤s le)) (fd-mUnit e P u) = fd-mUnit (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) P) (FragD-mono (s≤s le) u)
FragD-mono (s≤s (s≤s le)) (fd-idt A a b) = fd-idt (FragD-mono (s≤s le) A) (FragD-mono (s≤s le) a) (FragD-mono (s≤s le) b)
FragD-mono (s≤s le) fd-rfl = fd-rfl
FragD-mono (s≤s (s≤s le)) (fd-rwt e P t) = fd-rwt (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) P) (FragD-mono (s≤s le) t)
FragD-mono (s≤s le) fd-def = fd-def
FragD-mono (s≤s (s≤s le)) (fd-ann e A) = fd-ann (FragD-mono (s≤s le) e) (FragD-mono (s≤s le) A)
FragDL-mono le fdl-[] = fdl-[]
FragDL-mono (s≤s le) (fdl-∷ t ts) = fdl-∷ (FragD-mono (s≤s le) t) (FragDL-mono (s≤s le) ts)

FragD-suc : ∀ {n d} {t : Tm n} → FragD d t → FragD (suc d) t
FragD-suc = FragD-mono (n≤1+n _)

FragDL-suc : ∀ {n d} {ts : List (Tm n)} → FragDL d ts → FragDL (suc d) ts
FragDL-suc = FragDL-mono (n≤1+n _)

-- every fragment term has a depth
Frag→FragD : ∀ {n} {t : Tm n} → Frag t → ∃ λ d → FragD d t
FragL→FragDL : ∀ {n} {ts : List (Tm n)} → FragL ts → ∃ λ d → FragDL d ts

join₂ : ∀ {n m} {A : Tm n} {B : Tm m} → (∃ λ d → FragD d A) → (∃ λ d → FragD d B)
  → ∃ λ d → FragD d A × FragD d B
join₂ (d₁ , F₁) (d₂ , F₂) = d₁ ⊔ d₂ , FragD-mono (m≤m⊔n d₁ d₂) F₁ , FragD-mono (m≤n⊔m d₁ d₂) F₂

Frag→FragD f-var = 1 , fd-var
Frag→FragD f-typ = 1 , fd-typ
Frag→FragD (f-pi A B) with join₂ (Frag→FragD A) (Frag→FragD B)
... | d , A′ , B′ = suc (suc d) , fd-pi (FragD-suc A′) (FragD-suc B′)
Frag→FragD (f-lam A t) with join₂ (Frag→FragD A) (Frag→FragD t)
... | d , A′ , t′ = suc (suc d) , fd-lam (FragD-suc A′) (FragD-suc t′)
Frag→FragD (f-app f a) with join₂ (Frag→FragD f) (Frag→FragD a)
... | d , f′ , a′ = suc (suc d) , fd-app (FragD-suc f′) (FragD-suc a′)
Frag→FragD f-nat = 1 , fd-nat
Frag→FragD f-ze = 1 , fd-ze
Frag→FragD (f-su t) with Frag→FragD t
... | d , t′ = suc (suc d) , fd-su (FragD-suc t′)
Frag→FragD f-unit = 1 , fd-unit
Frag→FragD f-one = 1 , fd-one
Frag→FragD f-empty = 1 , fd-empty
Frag→FragD f-dty = 1 , fd-dty
Frag→FragD f-ctor = 1 , fd-ctor
Frag→FragD (f-mData e P bs) with join₂ (Frag→FragD e) (Frag→FragD P) | FragL→FragDL bs
... | d₁ , e′ , P′ | d₂ , bs′ = suc (suc (d₁ ⊔ d₂))
  , fd-mData (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) e′)) (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) P′)) (FragDL-suc (FragDL-mono (m≤n⊔m d₁ d₂) bs′))
Frag→FragD (f-mNat e P z s) with join₂ (Frag→FragD e) (Frag→FragD P) | join₂ (Frag→FragD z) (Frag→FragD s)
... | d₁ , e′ , P′ | d₂ , z′ , s′ = suc (suc (d₁ ⊔ d₂))
  , fd-mNat (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) e′)) (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) P′))
            (FragD-suc (FragD-mono (m≤n⊔m d₁ d₂) z′)) (FragD-suc (FragD-mono (m≤n⊔m d₁ d₂) s′))
Frag→FragD (f-mEmp e P) with join₂ (Frag→FragD e) (Frag→FragD P)
... | d , e′ , P′ = suc (suc d) , fd-mEmp (FragD-suc e′) (FragD-suc P′)
Frag→FragD (f-mUnit e P u) with join₂ (Frag→FragD e) (Frag→FragD P) | Frag→FragD u
... | d₁ , e′ , P′ | d₂ , u′ = suc (suc (d₁ ⊔ d₂))
  , fd-mUnit (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) e′)) (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) P′)) (FragD-suc (FragD-mono (m≤n⊔m d₁ d₂) u′))
Frag→FragD (f-idt A a b) with join₂ (Frag→FragD A) (Frag→FragD a) | Frag→FragD b
... | d₁ , A′ , a′ | d₂ , b′ = suc (suc (d₁ ⊔ d₂))
  , fd-idt (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) A′)) (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) a′)) (FragD-suc (FragD-mono (m≤n⊔m d₁ d₂) b′))
Frag→FragD f-rfl = 1 , fd-rfl
Frag→FragD (f-rwt e P t) with join₂ (Frag→FragD e) (Frag→FragD P) | Frag→FragD t
... | d₁ , e′ , P′ | d₂ , t′ = suc (suc (d₁ ⊔ d₂))
  , fd-rwt (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) e′)) (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) P′)) (FragD-suc (FragD-mono (m≤n⊔m d₁ d₂) t′))
Frag→FragD f-def = 1 , fd-def
Frag→FragD (f-ann e A) with join₂ (Frag→FragD e) (Frag→FragD A)
... | d , e′ , A′ = suc (suc d) , fd-ann (FragD-suc e′) (FragD-suc A′)
FragL→FragDL fl-[] = 1 , fdl-[]
FragL→FragDL (fl-∷ t ts) with Frag→FragD t | FragL→FragDL ts
... | d₁ , t′ | d₂ , ts′ = suc (d₁ ⊔ d₂) , fdl-∷ (FragD-suc (FragD-mono (m≤m⊔n d₁ d₂) t′)) (FragDL-suc (FragDL-mono (m≤n⊔m d₁ d₂) ts′))

-- the arguments of a spine are shallower than the spine
FragDL-snoc : ∀ {n d} {ts : List (Tm n)} {t} → FragDL (suc d) ts → FragD (suc d) t → FragDL (suc d) (ts ++ (t ∷ []))
FragDL-snoc fdl-[] F = fdl-∷ F fdl-[]
FragDL-snoc (fdl-∷ t ts) F = fdl-∷ t (FragDL-snoc ts F)

FragD-Spine : ∀ {n d} {h : Tm n} {as e} → FragD (suc d) e → Spine h as e → FragDL d as
FragD-Spine F sp-[] = fdl-[]
FragD-Spine (fd-app Ff Fa) (sp-snoc sp) = FragDL-snoc (FragDL-suc (FragD-Spine Ff sp)) Fa

-- every depth is positive
FragD-pos : ∀ {n d} {e : Tm n} → FragD d e → ∃ λ d′ → d ≡ suc d′
FragD-pos fd-var = _ , refl
FragD-pos fd-typ = _ , refl
FragD-pos (fd-pi _ _) = _ , refl
FragD-pos (fd-lam _ _) = _ , refl
FragD-pos (fd-app _ _) = _ , refl
FragD-pos fd-nat = _ , refl
FragD-pos fd-ze = _ , refl
FragD-pos (fd-su _) = _ , refl
FragD-pos fd-unit = _ , refl
FragD-pos fd-one = _ , refl
FragD-pos fd-empty = _ , refl
FragD-pos fd-dty = _ , refl
FragD-pos fd-ctor = _ , refl
FragD-pos (fd-mData _ _ _) = _ , refl
FragD-pos (fd-mNat _ _ _ _) = _ , refl
FragD-pos (fd-mEmp _ _) = _ , refl
FragD-pos (fd-mUnit _ _ _) = _ , refl
FragD-pos (fd-idt _ _ _) = _ , refl
FragD-pos fd-rfl = _ , refl
FragD-pos (fd-rwt _ _ _) = _ , refl
FragD-pos fd-def = _ , refl
FragD-pos (fd-ann _ _) = _ , refl

------------------------------------------------------------------------
-- Part 4: the checker is sound for ⊢. If infer / check / checkTy say
-- yes on fragment input over a covered signature, ⊢ has a derivation
-- with the same uses; the inferred type agrees up to ≈ (Check returns
-- the motive of a match as a β-redex).
------------------------------------------------------------------------

infer-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → FragD (suc d) e
  → infer k σ rs Γ m e ≡ ok (A , u)
  → Frag A × ∃ λ A′ → (σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u) × (σ ⊢[ spec ] A′ ≈ A)
check-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → FragD (suc d) e → Frag A
  → check k σ rs Γ m e A ≡ ok u → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
checkTy-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} {A} → GoodSig σ → FragCtx Γ → FragD (suc d) A
  → checkTy k σ rs Γ A ≡ ok tt → σ , Γ ⊢ A wf
checkAgainst-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → FragD (suc d) e → Frag A
  → checkAgainst k σ rs Γ m e A (viewData k σ A) (ctorSpine e) ≡ ok u
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
inferConv-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A B u} → GoodSig σ → FragCtx Γ → FragD (suc d) e → Frag A
  → infer k σ rs Γ m e ≡ ok (B , u) → conv k σ B A ≡ ok tt
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
checkCtorArgs-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di np ty as X u} → GoodSig σ → FragCtx Γ
  → Frag ty → FragDL (suc d) as → Frag X → Tel di np ty
  → checkCtorArgs k σ rs Γ m ty as X ≡ ok u
  → ∃ λ R → (σ , Γ ⊢[ m ] ty ▹ as ⇝ R ⊣ u) × (σ ⊢[ spec ] R ≈ X)
-- the arguments of a constructor spine, one level down (the spine is
-- taken apart here, by pattern matching, so the depth decreases in a
-- clause head)
ctorArgs-spine : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di np ty i j as e X u} → GoodSig σ → FragCtx Γ
  → Frag ty → FragD (suc d) e → Spine (ctor i j) as e → Frag X → Tel di np ty
  → checkCtorArgs k σ rs Γ m ty as X ≡ ok u
  → ∃ λ R → (σ , Γ ⊢[ m ] ty ▹ as ⇝ R ⊣ u) × (σ ⊢[ spec ] R ≈ X)
checkBr-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m di ci {np ty br D P args forces u} → GoodSig σ → FragCtx Γ
  → Frag ty → FragD (suc d) br → Frag D → Frag P → FragL args → Tel di np ty → nparamsOf σ di ≡ np
  → forces ≡ noForces ty
  → checkBr k σ rs Γ m di ci ty br (lam affine D P) args forces ≡ ok u
  → ∃ λ X → BrTy σ di ci ty P args X × (σ , Γ ⊢[ m ] br ⇐ X ⊣ u)
checkBranches-sound : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} m di {np params D P ci cs bs u} → GoodSig σ → FragCtx Γ
  → FragL params → Frag D → Frag P → FragDL (suc d) bs → CtorsOk di np cs → nparamsOf σ di ≡ np
  → checkBranches k σ rs Γ m di params [] (lam affine D P) ci cs bs ≡ ok u
  → σ , Γ ⊢[ m ] bs brs⟨ di , params , P , ci ⟩ cs ⊣ u


------------------------------------------------------------------------
-- Small helpers for the main proof.
------------------------------------------------------------------------

-- if q is +, the domain was checked to be Data
reuseOk-sound : ∀ k σ {n} {A : Tm n} {s y} q → FragSig σ → Frag A
  → (if eqQty q reuse then guard s (isData k σ A) else ok tt) ≡ ok y → ReuseOk σ q A
reuseOk-sound k σ affine fs FA _ = tt
reuseOk-sound k σ erased fs FA _ = tt
reuseOk-sound k σ reuse fs FA eq = isData-sound k σ fs FA (guard-ok eq)

var-run : ∀ {σ n} {Γ : Ctx n} {x q} → qtyOf Γ x ≡ q → (q ≡ erased → ⊥)
  → σ , Γ ⊢[ run ] var x ⇒ typOf Γ x ⊣ oneHot x (if eqQty q reuse then Uω else U1)
var-run refl ne = ⇒-var-run ne

var-evid : ∀ {σ n} {Γ : Ctx n} {x q} → qtyOf Γ x ≡ q → (q ≡ erased → ⊥)
  → σ , Γ ⊢[ evid ] var x ⇒ typOf Γ x ⊣ oneHot x (if eqQty q reuse then Uω else U1)
var-evid refl ne = ⇒-var-evid ne

eqMode-sound : ∀ m m′ → eqMode m m′ ≡ true → m ≡ m′
eqMode-sound run run _ = refl
eqMode-sound evid evid _ = refl
eqMode-sound spec spec _ = refl

combineArg-era : ∀ {n} m (au asu : UseVec n)
  → combineArg erased m au asu ≡ (if eqMode m spec then ok u0s else ok asu)
combineArg-era run _ _ = refl
combineArg-era evid _ _ = refl
combineArg-era spec _ _ = refl

-- the recursion state Check uses under a λ / a match binder
lamRec : ∀ {n} → RecSt n → Qty → RecSt (suc n)
lamRec rs q =
  let rs1 = extRec rs false (RecSt.nextOk rs)
  in if eqQty q erased then keepNext rs rs1 else rs1

brRec : ∀ {n} → RecSt n → Qty → ℕ → Tm n → RecSt (suc n)
brRec rs q di A =
  let rec? = isDType di A
      rs1  = extRec rs rec? rec?
  in if eqQty q erased then keepNext rs rs1 else rs1

viewPi-≈ : ∀ k σ {n} {T : Tm n} {q A B} → FragSig σ → Frag T
  → viewPi k σ T ≡ ok (q , A , B) → σ ⊢[ spec ] T ≈ pi q A B
viewPi-≈ k σ fs FT eq = ≈-trans (whnf-≈ k σ fs FT) (≈-≡ (viewPi-sound k σ eq))

viewPi-Frag : ∀ k σ {n} {T : Tm n} {q A B} → FragSig σ → Frag T
  → viewPi k σ T ≡ ok (q , A , B) → Frag A × Frag B
viewPi-Frag k σ fs FT eq with subst Frag (viewPi-sound k σ eq) (whnf-Frag k σ fs FT)
... | f-pi FA FB = FA , FB

viewId-≈ : ∀ k σ {n} {T : Tm n} {A a b} → FragSig σ → Frag T
  → viewId k σ T ≡ ok (A , a , b) → σ ⊢[ spec ] T ≈ idt A a b
viewId-≈ k σ fs FT eq = ≈-trans (whnf-≈ k σ fs FT) (≈-≡ (viewId-sound k σ eq))

viewId-Frag : ∀ k σ {n} {T : Tm n} {A a b} → FragSig σ → Frag T
  → viewId k σ T ≡ ok (A , a , b) → Frag A × Frag a × Frag b
viewId-Frag k σ fs FT eq with subst Frag (viewId-sound k σ eq) (whnf-Frag k σ fs FT)
... | f-idt FA Fa Fb = FA , Fa , Fb

------------------------------------------------------------------------
-- inferConv: infer then convert (Check's default for ⇐).
------------------------------------------------------------------------

inferConv-sound d k σ rs m G FΓ Fe FA ieq ceq with infer-sound d k σ rs m G FΓ Fe ieq
... | FB , A′ , D , c = ⇐-conv D (≈-trans c (conv-sound k σ (GoodSig.frag G) FB FA ceq))

------------------------------------------------------------------------
-- infer
------------------------------------------------------------------------

-- var
infer-sound d k σ rs {Γ = Γ} run G FΓ (fd-var {x = x}) eq with qtyOf Γ x in qeq
... | erased = ⊥-elim (fail≢ok eq)
... | affine with isRunType k σ (typOf Γ x)
...   | false = ⊥-elim (fail≢ok eq)
...   | true with ok-inj eq
...     | refl = FΓ x , _ , var-run qeq (λ ()) , ≈-refl
infer-sound d k σ rs {Γ = Γ} run G FΓ (fd-var {x = x}) eq | reuse with isRunType k σ (typOf Γ x)
...   | false = ⊥-elim (fail≢ok eq)
...   | true with ok-inj eq
...     | refl = FΓ x , _ , var-run qeq (λ ()) , ≈-refl
infer-sound d k σ rs {Γ = Γ} evid G FΓ (fd-var {x = x}) eq with qtyOf Γ x in qeq
... | erased = ⊥-elim (fail≢ok eq)
... | affine with ok-inj eq
...   | refl = FΓ x , _ , var-evid qeq (λ ()) , ≈-refl
infer-sound d k σ rs {Γ = Γ} evid G FΓ (fd-var {x = x}) eq | reuse with ok-inj eq
...   | refl = FΓ x , _ , var-evid qeq (λ ()) , ≈-refl
infer-sound d k σ rs spec G FΓ (fd-var {x = x}) refl = FΓ x , _ , ⇒-var-spec , ≈-refl

-- Type has no type
infer-sound d k σ rs run G FΓ fd-typ eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs evid G FΓ fd-typ eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs spec G FΓ fd-typ eq = ⊥-elim (fail≢ok eq)

-- Π
infer-sound (suc d) k σ rs run G FΓ (fd-pi _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound (suc d) k σ rs evid G FΓ (fd-pi _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound (suc d) k σ rs {Γ = Γ} spec G FΓ (fd-pi {q = q} {A = A} {B = B} FA FB) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with check k σ (extRec rs false false) (ext Γ q A) spec B typ in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok u′ with ok-inj eq
...     | refl = f-typ , _
      , ⇒-pi (checkTy-sound d k σ rs G FΓ FA teq)
             (check-sound d k σ (extRec rs false false) spec G (FragCtx-ext FΓ (FragD→Frag FA)) FB f-typ beq)
      , ≈-refl

-- λ
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-lam {q = q} {A = A} {t = t} FA Ft) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with (if eqQty q reuse then guard "+ requires a Data type" (isData k σ A) else ok tt) in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with infer k σ (lamRec rs q) (ext Γ q A) m t in ieq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (B , u₀ Vec.∷ us) with checkBound m q u₀ in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with ok-inj eq
...         | refl with infer-sound d k σ (lamRec rs q) m G (FragCtx-ext FΓ (FragD→Frag FA)) Ft ieq
...           | FB , B′ , D , c = f-pi (FragD→Frag FA) FB , _
            , ⇒-lam (checkTy-sound d k σ rs G FΓ FA teq) (reuseOk-sound k σ q (GoodSig.frag G) (FragD→Frag FA) req) D beq
            , ≈-pi ≈-refl c

-- application
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-app {f = f} {a = a} Ff Fa) eq with infer k σ rs Γ m f in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (ft , fu) with viewPi k σ ft in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (affine , A , B) with check k σ rs Γ m a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok au with appUses σ m f fu au in ueq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok uses with checkRec k σ m rs (app f a)
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok _ with ok-inj eq
...           | refl with infer-sound d k σ rs m G FΓ Ff feq
...             | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB = Frag-inst FB (FragD→Frag Fa) , _
                , ⇒-app-aff Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                    (check-sound d k σ rs m G FΓ Fa FA aeq) ueq
                , ≈-refl
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (reuse , A , B) with isData k σ A in deq
...     | false = ⊥-elim (fail≢ok eq)
...     | true with check k σ rs Γ m a A in aeq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok au with appUses σ m f fu au in ueq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok uses with checkRec k σ m rs (app f a)
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok _ with ok-inj eq
...             | refl with infer-sound d k σ rs m G FΓ Ff feq
...               | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                 | FA , FB = Frag-inst FB (FragD→Frag Fa) , _
                  , ⇒-app-reuse Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                      (isData-sound k σ (GoodSig.frag G) FA deq)
                      (check-sound d k σ rs m G FΓ Fa FA aeq) ueq
                  , ≈-refl
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) with check k σ rs Γ spec a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok au with eqMode m spec in meq
...       | true with eqMode-sound m spec meq
...         | refl with ok-inj eq
...           | refl with infer-sound d k σ rs spec G FΓ Ff feq
...             | Fft , F′ , Df , c with spec-⇒-uses Df
...               | refl with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                 | FA , FB = Frag-inst FB (FragD→Frag Fa) , _
                  , ⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                      (check-sound d k σ rs spec G FΓ Fa FA aeq)
                  , ≈-refl
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) | ok au | false
  with checkRec k σ m rs (app f a)
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok _ with ok-inj eq
...           | refl with infer-sound d k σ rs m G FΓ Ff feq
...             | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB = Frag-inst FB (FragD→Frag Fa) , _
                , ⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                    (check-sound d k σ rs spec G FΓ Fa FA aeq)
                , ≈-refl

-- Nat
infer-sound d k σ rs run G FΓ fd-nat eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs evid G FΓ fd-nat eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs spec G FΓ fd-nat refl = f-typ , _ , ⇒-nat , ≈-refl
infer-sound d k σ rs m G FΓ fd-ze refl = f-nat , _ , ⇒-ze , ≈-refl
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-su {t = t} Ft) eq with check k σ rs Γ m t nat in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u′ with ok-inj eq
...   | refl = f-nat , _ , ⇒-su (check-sound d k σ rs m G FΓ Ft f-nat ceq) , ≈-refl

-- Unit, Empty
infer-sound d k σ rs run G FΓ fd-unit eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs evid G FΓ fd-unit eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs spec G FΓ fd-unit refl = f-typ , _ , ⇒-unit , ≈-refl
infer-sound d k σ rs m G FΓ fd-one refl = f-unit , _ , ⇒-one , ≈-refl
infer-sound d k σ rs run G FΓ fd-empty eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs evid G FΓ fd-empty eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs spec G FΓ fd-empty refl = f-typ , _ , ⇒-empty , ≈-refl

-- data former, constructor
infer-sound d k σ rs run G FΓ fd-dty eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs evid G FΓ fd-dty eq = ⊥-elim (fail≢ok eq)
infer-sound d k σ rs spec G FΓ (fd-dty {i = i}) eq with lookupData σ i in leq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok d with ok-inj eq
...   | refl = Frag-dtyType (DataDecl.pqtys d) (proj₁ (FragSig.datas (GoodSig.frag G) i d leq)) , _
            , ⇒-dty leq , ≈-refl
infer-sound d k σ rs m G FΓ fd-ctor eq = ⊥-elim (fail≢ok eq)

-- match on data
infer-sound (suc d₀) k σ rs {Γ = Γ} m G FΓ (fd-mData {e = e} {P = P} {bs = bs} Fe FP Fbs) eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (et , eu) with viewData k σ et in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (di , params , idxs) with viewData-sound k σ veq
...     | d , args , leq , sp , lenA , peq , ieq′
      with GoodSig.nonIdx G di d leq
...     | nidx
      with drop-all (nparams d) args
             (trans lenA (trans (cong (nparams d +_) (cong length nidx)) (+-identityʳ _)))
...     | dropA
      with trans ieq′ dropA
...     | refl
      rewrite leq | nidx
      with checkTy k σ (extRec rs false false) (ext Γ affine (appsFrom (dty di) params)) P in meq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt
      with checkBranches k σ rs Γ m di params [] (lam affine (appsFrom (dty di) params) P) 0 (DataDecl.ctors d) bs in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok bu with combine m eu bu in ceq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok uses with ok-inj eq
...           | refl with infer-sound d₀ k σ rs m G FΓ Fe ieq
...             | Fet , E′ , De , c =
  let fs = GoodSig.frag G
      Fargs = proj₂ (Frag-Spine sp (whnf-Frag k σ fs Fet))
      Fparams = subst FragL (sym peq) (FragL-take (nparams d) Fargs)
      FD = Frag-appsFrom f-dty Fparams
      params≡args : params ≡ args
      params≡args = trans peq (trans (sym (++-identityʳ _))
                      (trans (cong (take (nparams d) args ++_) (sym dropA)) (take++drop≡id (nparams d) args)))
      lps : length params ≡ nparams d
      lps = trans (cong length peq)
              (trans (length-take (nparams d) args)
                (trans (cong (nparams d ⊓_) lenA)
                  (m≤n⇒m⊓n≡m (m≤m+n (nparams d) 0))))
  in f-app (f-lam FD (FragD→Frag FP)) (FragD→Frag Fe) , _
   , ⇒-mData De
       (≈-trans c (≈-trans (whnf-≈ k σ fs Fet)
         (≈-≡ (trans (Spine-≡ sp) (cong (appsFrom (dty di)) (sym params≡args))))))
       leq nidx lps
       (checkTy-sound d₀ k σ (extRec rs false false) G (FragCtx-ext FΓ FD) FP meq)
       (checkBranches-sound d₀ k σ rs m di {np = nparams d} G FΓ Fparams FD (FragD→Frag FP) Fbs (ctorsOk {i = di} {d = d} G leq) (nparamsOf-ok {σ} {di} {d} leq) beq)
       ceq
   , ≈-sym β-mot

-- match on Nat
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-mNat {e = e} {P = P} {z = z} {s = s} Fe FP Fz Fs) eq with check k σ rs Γ m e nat in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine nat) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ m z (inst P ze) in zeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok zu with check k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) (ext Γ affine nat) m s (motSuc P) in seq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok (u₀ Vec.∷ sus) with checkBound m affine u₀ in beq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with combine m eu (combineAlt m zu sus) in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok uses with ok-inj eq
...             | refl = Frag-inst (FragD→Frag FP) (FragD→Frag Fe) , _
              , ⇒-mNat (check-sound d k σ rs m G FΓ Fe f-nat eeq)
                  (checkTy-sound d k σ (extRec rs false false) G (FragCtx-ext FΓ f-nat) FP peq)
                  (check-sound d k σ rs m G FΓ Fz (Frag-inst (FragD→Frag FP) f-ze) zeq)
                  (check-sound d k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) m G (FragCtx-ext FΓ f-nat) Fs (Frag-motSuc (FragD→Frag FP)) seq)
                  beq ceq
              , ≈-refl

-- match on Empty
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-mEmp {e = e} {P = P} Fe FP) eq with check k σ rs Γ m e empty in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine empty) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with ok-inj eq
...     | refl = Frag-inst (FragD→Frag FP) (FragD→Frag Fe) , _
      , ⇒-mEmp (check-sound d k σ rs m G FΓ Fe f-empty eeq)
          (checkTy-sound d k σ (extRec rs false false) G (FragCtx-ext FΓ f-empty) FP peq)
      , ≈-refl

-- match on Unit
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-mUnit {e = e} {P = P} {u = t} Fe FP Ft) eq with check k σ rs Γ m e unit in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine unit) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ m t (inst P one) in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok uu with combine m eu uu in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok uses with ok-inj eq
...         | refl = Frag-inst (FragD→Frag FP) (FragD→Frag Fe) , _
          , ⇒-mUnit (check-sound d k σ rs m G FΓ Fe f-unit eeq)
              (checkTy-sound d k σ (extRec rs false false) G (FragCtx-ext FΓ f-unit) FP peq)
              (check-sound d k σ rs m G FΓ Ft (Frag-inst (FragD→Frag FP) f-one) teq)
              ceq
          , ≈-refl

-- identity type, refl, rewrite
infer-sound (suc d) k σ rs run G FΓ (fd-idt _ _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound (suc d) k σ rs evid G FΓ (fd-idt _ _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound (suc d) k σ rs {Γ = Γ} spec G FΓ (fd-idt {A = A} {a = a} {b = b} FA Fa Fb) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with floatIdForbidden k σ A
...   | true = ⊥-elim (fail≢ok eq)
...   | false with check k σ rs Γ spec a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok ua with check k σ rs Γ spec b A in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok ub with ok-inj eq
...         | refl = f-typ , _
          , ⇒-idt (checkTy-sound d k σ rs G FΓ FA teq)
              (check-sound d k σ rs spec G FΓ Fa (FragD→Frag FA) aeq)
              (check-sound d k σ rs spec G FΓ Fb (FragD→Frag FA) beq)
          , ≈-refl
infer-sound d k σ rs m G FΓ fd-rfl eq = ⊥-elim (fail≢ok eq)
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-rwt {e = e} {P = P} {t = t} Fe FP Ft) eq with infer k σ rs Γ evid e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (et , eu) with viewId k σ et in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (A , l , r) with checkTy k σ (extRec rs false false) (ext Γ affine A) P in peq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with check k σ rs Γ m t (inst P r) in teq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tu with ok-inj eq
...         | refl with infer-sound d k σ rs evid G FΓ Fe ieq
...           | Fet , E′ , De , c with viewId-Frag k σ (GoodSig.frag G) Fet veq
...             | FA , Fl , Fr = Frag-inst (FragD→Frag FP) Fl , _
              , ⇒-rwt De (≈-trans c (viewId-≈ k σ (GoodSig.frag G) Fet veq))
                  (checkTy-sound d k σ (extRec rs false false) G (FragCtx-ext FΓ FA) FP peq)
                  (check-sound d k σ rs m G FΓ Ft (Frag-inst (FragD→Frag FP) Fr) teq)
              , ≈-refl

-- definitions
infer-sound d k σ {n} rs m G FΓ (fd-def {i = i}) eq with lookupDef σ i in leq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok d with allowedDef (Def.dmode d) m in aeq
...   | false = ⊥-elim (fail≢ok eq)
...   | true with eqMode m run ∧ not (isRunType k σ (closed {n} (Def.dtype d)))
...     | true = ⊥-elim (fail≢ok eq)
...     | false with ok-inj eq
...       | refl = Frag-closed (proj₁ (FragSig.defs (GoodSig.frag G) i d leq)) , _
                 , ⇒-def leq aeq , ≈-refl

-- annotation
infer-sound (suc d) k σ rs {Γ = Γ} m G FΓ (fd-ann {e = e} {A = A} Fe FA) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with check k σ rs Γ m e A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok u′ with ok-inj eq
...     | refl = FragD→Frag FA , _
      , ⇒-ann (checkTy-sound d k σ rs G FΓ FA teq) (check-sound d k σ rs m G FΓ Fe (FragD→Frag FA) ceq)
      , ≈-refl

------------------------------------------------------------------------
-- check
------------------------------------------------------------------------

-- λ against a type: viewPi, or infer and convert. The head does not
-- split the fragment witness (that would fix the depth to suc d′ and
-- every call inside the with-chain would have to rebuild it); Fe is
-- split only where the body is checked.
check-sound d k σ rs {Γ = Γ} m {e = lam q A t} {A = T} G FΓ Fe FT eq with viewPi k σ T in peq
... | fail _ with infer k σ rs Γ m (lam q A t) in ieq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (B , u′) with conv k σ B T in ceq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with ok-inj eq
...       | refl = inferConv-sound d k σ rs m G FΓ Fe FT ieq ceq
check-sound d k σ rs {Γ = Γ} m {e = lam q A t} {A = T} G FΓ Fe FT eq | ok (q′ , A′ , B) with eqQty q q′ in qeq
...   | false = ⊥-elim (fail≢ok eq)
...   | true with eqQty-sound q q′ qeq
...     | refl with checkTy k σ rs Γ A in teq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with conv k σ A A′ in ceq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with (if eqQty q reuse then guard "+ requires a Data type" (isData k σ A′) else ok tt) in req
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with check k σ (lamRec rs q) (ext Γ q A′) m t B in beq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...               | fail _ = ⊥-elim (fail≢ok eq)
...               | ok tt with ok-inj eq
...                 | refl with viewPi-Frag k σ (GoodSig.frag G) FT peq
...                   | FA′ , FB with Fe
...                     | fd-lam {d = d′} FA Ft =
  ⇐-lam (checkTy-sound d′ k σ rs G FΓ FA teq) (viewPi-≈ k σ (GoodSig.frag G) FT peq)
    (conv-sound k σ (GoodSig.frag G) (FragD→Frag FA) FA′ ceq) (reuseOk-sound k σ q (GoodSig.frag G) FA′ req)
    (check-sound d′ k σ (lamRec rs q) m G (FragCtx-ext FΓ FA′) Ft FB beq) bq

-- refl against a type
check-sound d k σ rs {Γ = Γ} m {A = T} G FΓ fd-rfl FT eq with viewId k σ T in veq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , a , b) with floatIdForbidden k σ A
...   | true = ⊥-elim (fail≢ok eq)
...   | false with conv k σ a b in ceq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with ok-inj eq
...       | refl with viewId-Frag k σ (GoodSig.frag G) FT veq
...         | FA , Fa , Fb = ⇐-refl (viewId-≈ k σ (GoodSig.frag G) FT veq) (conv-sound k σ (GoodSig.frag G) Fa Fb ceq)

-- everything else: checkAgainst
check-sound d k σ rs m G FΓ Fe@fd-var FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-typ FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-pi _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-app _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-nat FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-ze FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-su _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-unit FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-one FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-empty FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-dty FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-ctor FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-mData _ _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-mNat _ _ _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-mEmp _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-mUnit _ _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-idt _ _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-rwt _ _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@fd-def FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq
check-sound d k σ rs m G FΓ Fe@(fd-ann _ _) FA eq = checkAgainst-sound d k σ rs m G FΓ Fe FA eq

------------------------------------------------------------------------
-- checkAgainst: a constructor spine against a data type, else infer.
------------------------------------------------------------------------

checkAgainst-sound d₀ k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq with viewData k σ A in veq | ctorSpine e in ceq
... | fail _ | _ with infer k σ rs Γ m e in ieq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (B , u′) with conv k σ B A in cveq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with ok-inj eq
...       | refl = inferConv-sound d₀ k σ rs m G FΓ Fe FA ieq cveq
checkAgainst-sound d₀ k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq | ok _ | nothing with infer k σ rs Γ m e in ieq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (B , u′) with conv k σ B A in cveq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with ok-inj eq
...       | refl = inferConv-sound d₀ k σ rs m G FΓ Fe FA ieq cveq
checkAgainst-sound d₀ k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq | ok (di , params , idxs) | just (di′ , ci , args) with di ≡ᵇ di′ in deq
...   | false with infer k σ rs Γ m e in ieq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (B , u′) with conv k σ B A in cveq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with ok-inj eq
...         | refl = inferConv-sound d₀ k σ rs m G FΓ Fe FA ieq cveq
checkAgainst-sound d₀ k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq | ok (di , params , idxs) | just (di′ , ci , args) | true with ≡ᵇ-sound {di} {di′} deq
...     | refl with viewData-sound k σ veq
...       | d , args′ , leq , sp′ , lenA , peq , ieq′ rewrite leq with lookupCtor d ci in keq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok c with instParams k σ (closed (Ctor.ctype c)) params in ipeq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok rest
            with instParams-sound k σ (GoodSig.frag G)
                   (Frag-closed (FragCtors-lookup (proj₂ (FragSig.datas (GoodSig.frag G) di d leq)) keq))
                   (subst FragL (sym peq) (FragL-take (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA)))))
                   (Tel-ren fromZero (GoodSig.tel G di d leq ci c keq)) ipeq
...             | ip , Frest , tlR
              with ctorArgs-spine d₀ k σ rs m G FΓ Frest Fe (ctorSpine-just ceq)
                     (Frag-appsFrom f-dty (FragL-++
                       (subst FragL (sym peq) (FragL-take (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA)))))
                       (subst FragL (sym ieq′) (FragL-drop (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA)))))))
                     tlR eq
...                 | R , Ar , cR =
  let pieq : params ++ idxs ≡ args′
      pieq = trans (cong₂ _++_ peq ieq′) (take++drop≡id (nparams d) args′)
      lps : length params ≡ nparams d
      lps = trans (cong length peq)
              (trans (length-take (nparams d) args′)
                (trans (cong (nparams d ⊓_) lenA) (m≤n⇒m⊓n≡m (m≤m+n (nparams d) (nidxs d)))))
      lidx : length idxs ≡ nidxs d
      lidx = trans (cong length ieq′)
               (trans (length-drop (nparams d) args′)
                 (trans (cong (_∸ nparams d) lenA) (m+n∸m≡n (nparams d) (nidxs d))))
  in ⇐-ctor (ctorSpine-just ceq)
       (≈-trans (whnf-≈ k σ (GoodSig.frag G) FA)
         (≈-≡ (trans (Spine-≡ sp′) (cong (appsFrom (dty di)) (sym pieq)))))
       leq lps lidx keq ip Ar cR

------------------------------------------------------------------------
-- checkCtorArgs: along the constructor telescope.
------------------------------------------------------------------------

checkCtorArgs-sound d k σ rs m G FΓ Fty fdl-[] FX (tel-pi {q = q} {A = A} {B} tl) eq
  rewrite whnf-pi k σ {q = q} {A = A} {B = B} = ⊥-elim (fail≢ok eq)
checkCtorArgs-sound d k σ {n} rs {Γ = Γ} m {di} {X = X} G FΓ Fty fdl-[] FX (tel-end sp-[] len) eq
  rewrite whnf-dty k σ {n} {di} (sp-[] {h = dty di}) with conv k σ (dty di) X in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with ok-inj eq
...   | refl = _ , args-[] , conv-sound k σ (GoodSig.frag G) Fty FX ceq
checkCtorArgs-sound d k σ rs {Γ = Γ} m {X = X} G FΓ Fty fdl-[] FX (tel-end (sp-snoc {f = f} {a = a} sp) len) eq
  rewrite whnf-dty k σ (sp-snoc {a = a} sp) with conv k σ (app f a) X in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with ok-inj eq
...   | refl = _ , args-[] , conv-sound k σ (GoodSig.frag G) Fty FX ceq
checkCtorArgs-sound d k σ {n} rs m {di} G FΓ Fty (fdl-∷ Fa Fas) FX (tel-end sp-[] len) eq
  rewrite whnf-dty k σ {n} {di} (sp-[] {h = dty di}) = ⊥-elim (fail≢ok eq)
checkCtorArgs-sound d k σ rs m G FΓ Fty (fdl-∷ Fa Fas) FX (tel-end (sp-snoc {a = a} sp) len) eq
  rewrite whnf-dty k σ (sp-snoc {a = a} sp) = ⊥-elim (fail≢ok eq)
checkCtorArgs-sound d k σ rs {Γ = Γ} m {X = X} G FΓ (f-pi FA FB) (fdl-∷ {t = a} {ts = as′} Fa Fas) FX (tel-pi {q = affine} {A = A} {B} tl) eq
  rewrite whnf-pi k σ {q = affine} {A = A} {B = B} with check k σ rs Γ m a A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok au with checkCtorArgs k σ rs Γ m (inst B a) as′ X in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok asu with checkCtorArgs-sound d k σ rs m G FΓ (Frag-inst FB (FragD→Frag Fa)) Fas FX (Tel-sub _ tl) req
...     | R , Ar , cR = R , args-∷ ≈-refl (check-sound d k σ rs m G FΓ Fa FA aeq) Ar eq , cR
checkCtorArgs-sound d k σ rs {Γ = Γ} m {X = X} G FΓ (f-pi FA FB) (fdl-∷ {t = a} {ts = as′} Fa Fas) FX (tel-pi {q = reuse} {A = A} {B} tl) eq
  rewrite whnf-pi k σ {q = reuse} {A = A} {B = B} with check k σ rs Γ m a A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok au with checkCtorArgs k σ rs Γ m (inst B a) as′ X in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok asu with checkCtorArgs-sound d k σ rs m G FΓ (Frag-inst FB (FragD→Frag Fa)) Fas FX (Tel-sub _ tl) req
...     | R , Ar , cR = R , args-∷ ≈-refl (check-sound d k σ rs m G FΓ Fa FA aeq) Ar eq , cR
checkCtorArgs-sound d k σ rs {Γ = Γ} m {X = X} G FΓ (f-pi FA FB) (fdl-∷ {t = a} {ts = as′} Fa Fas) FX (tel-pi {q = erased} {A = A} {B} tl) eq
  rewrite whnf-pi k σ {q = erased} {A = A} {B = B} with check k σ rs Γ spec a A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok au with checkCtorArgs k σ rs Γ m (inst B a) as′ X in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok asu with checkCtorArgs-sound d k σ rs m G FΓ (Frag-inst FB (FragD→Frag Fa)) Fas FX (Tel-sub _ tl) req
...     | R , Ar , cR = R
      , args-∷ ≈-refl (check-sound d k σ rs spec G FΓ Fa FA aeq) Ar (trans (combineArg-era m au asu) eq)
      , cR

ctorArgs-spine d k σ rs m G FΓ Fty Fe sp-[] FX tl eq =
  checkCtorArgs-sound d k σ rs m G FΓ Fty fdl-[] FX tl eq
ctorArgs-spine (suc d) k σ rs m G FΓ Fty (fd-app Ff Fa) (sp-snoc sp) FX tl eq =
  checkCtorArgs-sound d k σ rs m G FΓ Fty (FragDL-snoc (FragDL-suc (FragD-Spine Ff sp)) Fa) FX tl eq

------------------------------------------------------------------------
-- checkBr: one branch along its constructor's telescope.
------------------------------------------------------------------------

checkBr-sound d k σ rs {Γ = Γ} m di ci {br = br} {D} {P} {args} G FΓ (f-pi FA FB) Fbr FD FP Fargs (tel-pi {q = q} {A = A} {B} tl) npeq refl eq
  rewrite whnf-pi k σ {q = q} {A = A} {B = B} with lamView br in leq
... | nothing = ⊥-elim (fail≢ok eq)
... | just (q′ , A′ , t) with lamView-just leq
...   | refl with Fbr
...     | fd-lam {d = d′} FA′ Ft with eqQty q q′ in qeq
...       | false = ⊥-elim (fail≢ok eq)
...       | true with eqQty-sound q q′ qeq
...         | refl with checkTy k σ rs Γ A′ in teq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with conv k σ A′ A in ceq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok tt with (if eqQty q reuse then guard "+ requires a Data type" (isData k σ A) else ok tt) in req
...               | fail _ = ⊥-elim (fail≢ok eq)
...               | ok tt
                with checkBr k σ (brRec rs q di A) (ext Γ q A) m di ci B t (lam affine (wk D) (ren (lift suc) P))
                       (renList suc args ++ (var zero ∷ [])) (wkForces (noForces B)) in beq
...               | fail _ = ⊥-elim (fail≢ok eq)
...               | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...                 | fail _ = ⊥-elim (fail≢ok eq)
...                 | ok tt with ok-inj eq
...                   | refl
                  with checkBr-sound d′ k σ (brRec rs q di A) m di ci G (FragCtx-ext FΓ FA) FB Ft (Frag-wk FD)
                         (Frag-ren (lift suc) FP) (FragL-++ (FragL-ren suc Fargs) (fl-∷ f-var fl-[])) tl npeq
                         (wkForces-noForces (countPis B)) beq
...                   | X , bt , Dt =
  pi q A X
  , bt-pi ≈-refl (reuseOk-sound k σ q (GoodSig.frag G) FA req) bt
  , ⇐-lam (checkTy-sound d′ k σ rs G FΓ FA′ teq) ≈-refl (conv-sound k σ (GoodSig.frag G) (FragD→Frag FA′) FA ceq)
      (reuseOk-sound k σ q (GoodSig.frag G) FA req) Dt bq
checkBr-sound d k σ {n} rs {Γ = Γ} m di ci {np} {D = D} {P} {args} G FΓ Fty Fbr FD FP Fargs (tel-end {as = as} sp-[] len) npeq refl eq
  rewrite whnf-dty k σ {n} {di} (sp-[] {h = dty di}) | npeq | drop-all np as len =
  _ , bt-end sp-[] ≈-refl
    , ⇐-≈ (check-sound d k σ rs m G FΓ Fbr (f-app (f-lam FD FP) (Frag-appsFrom f-ctor Fargs)) eq) β-mot
checkBr-sound d k σ rs {Γ = Γ} m di ci {np} {D = D} {P} {args} G FΓ Fty Fbr FD FP Fargs (tel-end {as = as} (sp-snoc {a = a} sp) len) npeq refl eq
  rewrite whnf-dty k σ (sp-snoc {a = a} sp) | Spine→unspine head-dty (sp-snoc {a = a} sp) | npeq | drop-all np as len =
  _ , bt-end (sp-snoc sp) ≈-refl
    , ⇐-≈ (check-sound d k σ rs m G FΓ Fbr (f-app (f-lam FD FP) (Frag-appsFrom f-ctor Fargs)) eq) β-mot

------------------------------------------------------------------------
-- checkBranches: one branch per constructor, in order.
------------------------------------------------------------------------

checkBranches-sound d k σ rs m di G FΓ Fps FD FP fdl-[] co-[] npeq eq with ok-inj eq
... | refl = brs-[]
checkBranches-sound d k σ rs m di G FΓ Fps FD FP (fdl-∷ _ _) co-[] npeq eq = ⊥-elim (fail≢ok eq)
checkBranches-sound d k σ rs {Γ = Γ} m di {params = params} {D} {P} {ci} G FΓ Fps FD FP fdl-[] (co-∷ {c} {cs} Fc tlc rest) npeq eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq | analyzeForces-tel k σ tl = ⊥-elim (fail≢ok eq)
checkBranches-sound d k σ rs {Γ = Γ} m di {params = params} {D} {P} {ci} G FΓ Fps FD FP (fdl-∷ {t = b} {ts = bs} Fb Fbs′) (co-∷ {c} {cs} Fc tlc rest) npeq eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq | analyzeForces-tel k σ tl
      with checkBr k σ rs Γ m di ci ty b (lam affine D P) [] (noForces ty) in beq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok u with checkBranches k σ rs Γ m di params [] (lam affine D P) (suc ci) cs bs in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok v with ok-inj eq
...         | refl with checkBr-sound d k σ rs m di ci G FΓ Fty Fb FD FP fl-[] tl npeq refl beq
...           | X , bt , Db =
  brs-∷ ip bt Db (checkBranches-sound d k σ rs m di G FΓ Fps FD FP Fbs′ rest npeq ceq)

------------------------------------------------------------------------
-- checkTy: Type, a kind, or a small type (infer then conv with Type).
------------------------------------------------------------------------

checkTy-el : ∀ d k σ {n} (rs : RecSt n) {Γ : Ctx n} {A T u} → GoodSig σ → FragCtx Γ → FragD (suc d) A
  → infer k σ rs Γ spec A ≡ ok (T , u) → conv k σ T typ ≡ ok tt → σ , Γ ⊢ A wf
checkTy-el d k σ rs G FΓ FA ieq ceq with infer-sound d k σ rs spec G FΓ FA ieq
... | FT , T′ , D , c = type-el D (≈-trans c (conv-sound k σ (GoodSig.frag G) FT f-typ ceq))

checkTy-sound d k σ rs G FΓ fd-typ eq = type-Type
checkTy-sound (suc d) k σ rs {Γ = Γ} G FΓ (fd-pi {q = q} {A = A} {B = B} FA FB) eq with checkTy k σ rs Γ A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt = type-pi (checkTy-sound d k σ rs G FΓ FA aeq)
                      (checkTy-sound d k σ (extRec rs false false) G (FragCtx-ext FΓ (FragD→Frag FA)) FB eq)
-- infer reduces at once
checkTy-sound d k σ rs {Γ = Γ} G FΓ (fd-var {x = x}) eq = type-el ⇒-var-spec (conv-sound k σ (GoodSig.frag G) (FΓ x) f-typ eq)
checkTy-sound d k σ rs G FΓ fd-nat eq = type-el ⇒-nat (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound d k σ rs G FΓ fd-unit eq = type-el ⇒-unit (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound d k σ rs G FΓ fd-empty eq = type-el ⇒-empty (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound d k σ rs G FΓ fd-ze eq = type-el ⇒-ze (conv-sound k σ (GoodSig.frag G) f-nat f-typ eq)
checkTy-sound d k σ rs G FΓ fd-one eq = type-el ⇒-one (conv-sound k σ (GoodSig.frag G) f-unit f-typ eq)
checkTy-sound d k σ rs G FΓ fd-ctor eq = ⊥-elim (fail≢ok eq)
checkTy-sound d k σ rs G FΓ fd-rfl eq = ⊥-elim (fail≢ok eq)
-- infer is stuck on a subterm. The clauses match the term, not the
-- fragment witness, so that the depth stays a variable (see check-sound
-- on λ).
checkTy-sound d k σ rs {Γ = Γ} {A = A@(lam _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(app _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(su _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(dty _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(mData _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(mNat _ _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(mEmp _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(mUnit _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(idt _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(rwt _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(def _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq
checkTy-sound d k σ rs {Γ = Γ} {A = A@(ann _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el d k σ rs G FΓ Fe ieq eq

------------------------------------------------------------------------
-- Part 5: the statements over plain Frag (Frag→FragD supplies the
-- depth), and the corollaries for a definition and for a signature.
------------------------------------------------------------------------

infer-sound′ : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e
  → infer k σ rs Γ m e ≡ ok (A , u)
  → Frag A × ∃ λ A′ → (σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u) × (σ ⊢[ spec ] A′ ≈ A)
infer-sound′ k σ rs m G FΓ Fe eq with Frag→FragD Fe
... | d , Fd with FragD-pos Fd
...   | d′ , refl = infer-sound d′ k σ rs m G FΓ Fd eq

check-sound′ : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → check k σ rs Γ m e A ≡ ok u → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
check-sound′ k σ rs m G FΓ Fe FA eq with Frag→FragD Fe
... | d , Fd with FragD-pos Fd
...   | d′ , refl = check-sound d′ k σ rs m G FΓ Fd FA eq

checkTy-sound′ : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {A} → GoodSig σ → FragCtx Γ → Frag A
  → checkTy k σ rs Γ A ≡ ok tt → σ , Γ ⊢ A wf
checkTy-sound′ k σ rs G FΓ FA eq with Frag→FragD FA
... | d , Fd with FragD-pos Fd
...   | d′ , refl = checkTy-sound d′ k σ rs G FΓ Fd eq

-- The empty context is in the fragment.
FragCtx-[] : FragCtx Vec.[]
FragCtx-[] ()

tag-ok : ∀ {A : Set} {s} {r : Result A} {x} → tag s r ≡ ok x → r ≡ ok x
tag-ok {r = ok _}   eq = eq
tag-ok {r = fail _} ()

-- What ⊢ says of a definition Check accepts: its type is well-formed
-- and its body checks against it in the declared mode, with some uses.
DefOk : Sig → Def → Set
DefOk σ d = (σ , Vec.[] ⊢ Def.dtype d wf)
          × ∃ λ u → σ , Vec.[] ⊢[ Def.dmode d ] Def.dbody d ⇐ Def.dtype d ⊣ u

checkDef-sound : ∀ k σ i {d} → GoodSig σ → lookupDef σ i ≡ ok d
  → checkDef k σ i ≡ ok tt → DefOk σ d
checkDef-sound k σ i {d} G leq eq with lookupDef σ i in leq′
... | fail _ = ⊥-elim (fail≢ok leq)
... | ok d′ with ok-inj leq
...   | refl with >>-ok₃ eq
...     | (_ , teq) , (_ , beq) , _ , _ with FragSig.defs (GoodSig.frag G) i d′ leq′
...       | FT , FB =
  checkTy-sound′ k σ emptyRec G FragCtx-[] FT (ok-tt (tag-ok teq))
  , _ , check-sound′ k σ (defRec i) (Def.dmode d′) G FragCtx-[] FB FT (tag-ok beq)

checkDefs-sound : ∀ k σ j ds → checkDefs k σ j ds ≡ ok tt
  → ∀ i d → lookupList ds i ≡ ok d → checkDef k σ (j + i) ≡ ok tt
checkDefs-sound k σ j [] eq i d ()
checkDefs-sound k σ j (_ ∷ ds) eq zero d leq rewrite +-identityʳ j =
  ok-tt (proj₂ (proj₁ (>>-ok {r = checkDef k σ j} eq)))
checkDefs-sound k σ j (_ ∷ ds) eq (suc i) d leq rewrite +-suc j i =
  checkDefs-sound k σ (suc j) ds (proj₂ (>>-ok {r = checkDef k σ j} eq)) i d leq

-- The theorem for a whole signature: if Check accepts σ, every
-- definition of σ is derivable in ⊢.
checkSig-sound : ∀ k σ → GoodSig σ → checkSig k σ ≡ ok tt
  → ∀ i d → lookupDef σ i ≡ ok d → DefOk σ d
checkSig-sound k σ G eq i d leq =
  checkDef-sound k σ i G leq
    (checkDefs-sound k σ 0 (Sig.defs σ) (proj₂ (>>-ok {r = checkDatas k σ} eq)) i d leq)
