{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of the executable checker, part 2: the checker's views of a
-- type (viewPi, viewId, viewData), isData, and what the proof assumes
-- of the signature (GoodSig: fragment, non-indexed data, constructor
-- types are telescopes ending in the data type), with instParams and
-- analyzeForces on such a telescope.
------------------------------------------------------------------------

module Muro.Soundness.Views where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Spine
open import Muro.Frag
open import Muro.Reduction
open import Muro.Convert
open import Muro.Data hiding (subst₂)
open import Muro.Check
  using (whnf; apps; viewPi; viewId; viewData; splitData; isData; isDataN; allData;
         dataParamsData; instParams; analyzeForces; forcePairs; forcesFor; countPis;
         wkForces; lookupForce; matchIdxs; nparamsOf)
open import Muro.Typing using (typ-ext-suc)
open import Muro.Soundness.Conv

------------------------------------------------------------------------
-- Results.
------------------------------------------------------------------------

>>=-ok : ∀ {A B : Set} {r : Result A} {f : A → Result B} {x}
  → (r >>= f) ≡ ok x → ∃ λ y → (r ≡ ok y) × (f y ≡ ok x)
>>=-ok {r = ok y} eq = y , refl , eq

if-ok : ∀ {b s} {y : ⊤} → (if b then ok tt else fail s) ≡ ok y → b ≡ true
if-ok {true} _ = refl

------------------------------------------------------------------------
-- Terms whnf leaves alone: Π, and dty spines. (At zero fuel whnf fails,
-- so the statements are about what it returns when it returns.)
------------------------------------------------------------------------

whnf-pi : ∀ k σ {n q} {A : Tm n} {B r} → whnf k σ (pi q A B) ≡ ok r → r ≡ pi q A B
whnf-pi (suc k) σ eq = sym (ok-inj eq)

whnf-dty : ∀ k σ {n i} {as : List (Tm n)} {e r} → Spine (dty i) as e → whnf k σ e ≡ ok r → r ≡ e
whnf-dty (suc k) σ sp-[] eq = sym (ok-inj eq)
whnf-dty (suc k) σ (sp-snoc {f = f} sp) eq with whnf k σ f in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok f′ with whnf-dty k σ sp feq
whnf-dty (suc k) σ (sp-snoc sp-[]) eq | ok _ | refl = sym (ok-inj eq)
whnf-dty (suc k) σ (sp-snoc (sp-snoc _)) eq | ok _ | refl = sym (ok-inj eq)

------------------------------------------------------------------------
-- The views.
------------------------------------------------------------------------

viewPi-sound : ∀ k σ {n} {T : Tm n} {q A B}
  → viewPi k σ T ≡ ok (q , A , B) → whnf k σ T ≡ ok (pi q A B)
viewPi-sound k σ {T = T} eq with whnf k σ T
viewPi-sound k σ () | fail _
viewPi-sound k σ eq | ok (pi _ _ _) with ok-inj eq
... | refl = refl
viewPi-sound k σ () | ok (var _)
viewPi-sound k σ () | ok typ
viewPi-sound k σ () | ok (lam _ _ _)
viewPi-sound k σ () | ok (app _ _)
viewPi-sound k σ () | ok nat
viewPi-sound k σ () | ok ze
viewPi-sound k σ () | ok (su _)
viewPi-sound k σ () | ok unit
viewPi-sound k σ () | ok one
viewPi-sound k σ () | ok empty
viewPi-sound k σ () | ok (dty _)
viewPi-sound k σ () | ok (ctor _ _)
viewPi-sound k σ () | ok (mData _ _ _)
viewPi-sound k σ () | ok (mNat _ _ _ _)
viewPi-sound k σ () | ok (mEmp _ _)
viewPi-sound k σ () | ok (mUnit _ _ _)
viewPi-sound k σ () | ok (idt _ _ _)
viewPi-sound k σ () | ok rfl
viewPi-sound k σ () | ok (rwt _ _ _)
viewPi-sound k σ () | ok (def _)
viewPi-sound k σ () | ok (ann _ _)
viewPi-sound k σ () | ok (prod _ _)
viewPi-sound k σ () | ok (pair _ _)
viewPi-sound k σ () | ok (fst _)
viewPi-sound k σ () | ok (snd _)
viewPi-sound k σ () | ok (nu _)
viewPi-sound k σ () | ok (unf _ _)
viewPi-sound k σ () | ok (ucons _)
viewPi-sound k σ () | ok i64
viewPi-sound k σ () | ok f32ty
viewPi-sound k σ () | ok (tensor _ _)
viewPi-sound k σ () | ok (addi _ _)
viewPi-sound k σ () | ok (muli _ _)
viewPi-sound k σ () | ok (addt _ _)
viewPi-sound k σ () | ok (toi64 _)
viewPi-sound k σ () | ok (packi _ _)

viewId-sound : ∀ k σ {n} {T : Tm n} {A a b}
  → viewId k σ T ≡ ok (A , a , b) → whnf k σ T ≡ ok (idt A a b)
viewId-sound k σ {T = T} eq with whnf k σ T
viewId-sound k σ () | fail _
viewId-sound k σ eq | ok (idt _ _ _) with ok-inj eq
... | refl = refl
viewId-sound k σ () | ok (var _)
viewId-sound k σ () | ok typ
viewId-sound k σ () | ok (pi _ _ _)
viewId-sound k σ () | ok (lam _ _ _)
viewId-sound k σ () | ok (app _ _)
viewId-sound k σ () | ok nat
viewId-sound k σ () | ok ze
viewId-sound k σ () | ok (su _)
viewId-sound k σ () | ok unit
viewId-sound k σ () | ok one
viewId-sound k σ () | ok empty
viewId-sound k σ () | ok (dty _)
viewId-sound k σ () | ok (ctor _ _)
viewId-sound k σ () | ok (mData _ _ _)
viewId-sound k σ () | ok (mNat _ _ _ _)
viewId-sound k σ () | ok (mEmp _ _)
viewId-sound k σ () | ok (mUnit _ _ _)
viewId-sound k σ () | ok rfl
viewId-sound k σ () | ok (rwt _ _ _)
viewId-sound k σ () | ok (def _)
viewId-sound k σ () | ok (ann _ _)
viewId-sound k σ () | ok (prod _ _)
viewId-sound k σ () | ok (pair _ _)
viewId-sound k σ () | ok (fst _)
viewId-sound k σ () | ok (snd _)
viewId-sound k σ () | ok (nu _)
viewId-sound k σ () | ok (unf _ _)
viewId-sound k σ () | ok (ucons _)
viewId-sound k σ () | ok i64
viewId-sound k σ () | ok f32ty
viewId-sound k σ () | ok (tensor _ _)
viewId-sound k σ () | ok (addi _ _)
viewId-sound k σ () | ok (muli _ _)
viewId-sound k σ () | ok (addt _ _)
viewId-sound k σ () | ok (toi64 _)
viewId-sound k σ () | ok (packi _ _)

viewData-sound : ∀ k σ {n} {T : Tm n} {di ps idxs}
  → viewData k σ T ≡ ok (di , ps , idxs)
  → ∃ λ T′ → ∃ λ d → ∃ λ args
    → (whnf k σ T ≡ ok T′) × (lookupData σ di ≡ ok d) × Spine (dty di) args T′
    × (length args ≡ nparams d + nidxs d)
    × (ps ≡ take (nparams d) args) × (idxs ≡ drop (nparams d) args)
viewData-sound k σ {T = T} {di} {ps} {idxs} eq with whnf k σ T
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok T′ with dtyArgs T′ in deq
...   | nothing = ⊥-elim (fail≢ok eq)
...   | just (i , args) with lookupData σ i in leq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok d with length args ≡ᵇ (nparams d + nidxs d) in geq
...       | false = ⊥-elim (fail≢ok eq)
...       | true with ok-inj eq
...         | refl = T′ , d , args , refl , leq , dtyArgs-just deq , ≡ᵇ-sound geq , refl , refl

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

isData-sound : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t → isData k σ t ≡ ok true → IsData σ t
isDataN-sound : ∀ k σ {n} {t : Tm n} → FragSig σ → Frag t
  → isDataN k σ (apps t) ≡ ok true → IsData σ t
allData-sound : ∀ k σ {n} {ts : List (Tm n)} → FragSig σ → FragL ts
  → allData k σ ts ≡ ok true → AllData σ ts

allData-sound k σ fs fl-[] _ = ad-[]
allData-sound k σ fs (fl-∷ {t = t} F Fs) eq with isData k σ t in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok false = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
... | ok true = ad-∷ (isData-sound k σ fs F ieq) (allData-sound k σ fs Fs eq)

isData-sound (suc k) σ {t = t} fs Ft eq with whnf (suc k) σ t in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok t′ with whnf-sound (suc k) σ fs Ft weq
...   | r , F = d-conv (⟶*→≈ r) (isDataN-sound k σ fs F eq)

isDataN-sound k σ {t = t} fs Ft eq with unspine t in ueq
... | (nat , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = subst (IsData σ) (sym weq) d-nat
isDataN-sound k σ fs Ft eq | (unit , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = subst (IsData σ) (sym weq) d-unit
isDataN-sound k σ fs Ft eq | (empty , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = subst (IsData σ) (sym weq) d-empty
isDataN-sound k σ fs Ft eq | (i64 , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq Ft))
  where noFrag : ∀ {n} → Frag {n} i64 → ⊥
        noFrag ()
isDataN-sound k σ fs Ft eq | (f32ty , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq Ft))
  where noFrag : ∀ {n} → Frag {n} f32ty → ⊥
        noFrag ()
isDataN-sound k σ fs Ft eq | (tensor _ _ , []) with Spine-≡ (unspine→Spine′ ueq)
...   | weq = ⊥-elim (noFrag (subst Frag weq Ft))
  where noFrag : ∀ {n d s} → Frag {n} (tensor d s) → ⊥
        noFrag ()
isDataN-sound k σ {t = t} fs Ft eq | (dty i , as) with lookupData σ i in leq
...   | fail _ = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
...   | ok d with unspine→Spine′ ueq
...     | sp = d-dty leq sp (allData-sound k σ fs (FragL-take (nparams d) (proj₂ (Frag-Spine sp Ft))) eq)
isDataN-sound k σ fs Ft eq | ((var _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (typ , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((pi _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((lam _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((app _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (nat , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (ze , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((su _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (unit , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (one , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (empty , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((ctor _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((mData _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((mNat _ _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((mEmp _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((mUnit _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((idt _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (rfl , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((rwt _ _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((def _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((ann _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((prod _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((pair _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((fst _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((snd _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((nu _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((unf _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((ucons _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (i64 , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | (f32ty , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((tensor _ _) , _ ∷ _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((addi _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((muli _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((addt _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((toi64 _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()
isDataN-sound k σ fs Ft eq | ((packi _ _) , _) = ⊥-elim (false≢true (ok-inj eq))
  where false≢true : false ≡ true → ⊥
        false≢true ()

-- if q is +, the domain was checked to be Data
reuseOk-sound : ∀ k σ {n} {A : Tm n} {s y} q → FragSig σ → Frag A
  → (if eqQty q reuse then isData k σ A >>= guard s else ok tt) ≡ ok y → ReuseOk σ q A
reuseOk-sound k σ affine fs FA _ = tt
reuseOk-sound k σ erased fs FA _ = tt
reuseOk-sound k σ {A = A} reuse fs FA eq with isData k σ A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok false = ⊥-elim (fail≢ok eq)
... | ok true = isData-sound k σ fs FA ieq

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

-- whnf leaves a telescope alone (when it returns).
Tel-whnf : ∀ k σ {i np n} {T : Tm n} {r} → Tel i np T → whnf k σ T ≡ ok r → r ≡ T
Tel-whnf k σ (tel-pi _) eq = whnf-pi k σ eq
Tel-whnf k σ (tel-end sp _) eq = whnf-dty k σ sp eq

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
instParams-sound k σ {T = T} fs FT (fl-∷ Fp Fps) tl eq with whnf k σ T in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok T′ with Tel-whnf k σ tl weq
...   | refl with tl | FT
...     | tel-end sp-[] _ | _ = ⊥-elim (fail≢ok eq)
...     | tel-end (sp-snoc _) _ | _ = ⊥-elim (fail≢ok eq)
...     | tel-pi tl′ | f-pi FA FB
        with instParams-sound k σ fs (Frag-inst FB Fp) Fps (Tel-sub _ tl′) eq
...       | ip , FR , tlR = ip-∷ ≈-refl ip , FR , tlR

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

forcePairs-tel : ∀ k σ {n m} {np i d r} {T : Tm m} → Tel i np T
  → forcePairs {n} k σ np [] d T ≡ ok r → r ≡ just []
forcePairs-tel k σ (tel-pi tl) eq = forcePairs-tel k σ tl eq
forcePairs-tel k σ {m = m} {np = np} {i = i} (tel-end {as = as} sp-[] len) eq
  with whnf k σ (dty {m} i) in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok T′ with whnf-dty k σ {i = i} (sp-[] {h = dty i}) weq
...   | refl rewrite drop-all np as len = sym (ok-inj eq)
forcePairs-tel k σ {m = m} {np = np} (tel-end {as = as} (sp-snoc {f = f} {a = a} sp) len) eq
  with whnf k σ (app {m} f a) in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok T′ with whnf-dty k σ (sp-snoc {a = a} sp) weq
...   | refl rewrite Spine→unspine head-dty (sp-snoc {a = a} sp) | drop-all np as len = sym (ok-inj eq)

analyzeForces-tel : ∀ k σ {n np i r} {T : Tm n} → Tel i np T
  → analyzeForces k σ np [] T ≡ ok r → r ≡ just (noForces T)
analyzeForces-tel k σ {n = n} {np} {T = T} tl eq with forcePairs {n} k σ np [] 0 T in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok r′ with forcePairs-tel k σ tl feq
...   | refl = sym (ok-inj eq)

wkForces-noForces : ∀ {n} c → wkForces {n} (forcesFor c []) ≡ forcesFor c []
wkForces-noForces zero = refl
wkForces-noForces (suc c) = cong (nothing ∷_) (wkForces-noForces c)

FragCtx-ext : ∀ {n} {Γ : Ctx n} {q A} → FragCtx Γ → Frag A → FragCtx (ext Γ q A)
FragCtx-ext FΓ FA zero = Frag-wk FA
FragCtx-ext {Γ = Γ} {q} {A} FΓ FA (suc x) rewrite typ-ext-suc Γ q A x = Frag-wk (FΓ x)

-- A branch applied to the motive: Check writes the motive as a λ.
β-mot : ∀ {σ n q} {D : Tm n} {P e} → σ ⊢[ spec ] app (lam q D P) e ≈ inst P e
β-mot = ≈-step (⇛-β (⇛-refl _) (⇛-refl _))
