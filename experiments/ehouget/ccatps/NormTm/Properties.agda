------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties related to NormTm
------------------------------------------------------------------------

module NormTm.Properties where

open import Ty
open import Con
open import Tm
open import NormTm.Base
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_×_ to _∧_)
open import Data.Product.Properties

------------------------------------------------------------------------
-- NormTm constructors injectivity

norm-proj-injective : {n : ℕ} {Γ : Con n} {A : Ty n} {k : Fin n} {x y : A ► k}
                    → norm-proj {Γ = Γ} x ≡ norm-proj y → x ≡ y
norm-proj-injective refl = refl

norm-pair-injectiveˡ : {n : ℕ} {Γ : Con n} {X A B : Ty n}
                       {f g : NormTm Γ (X , A)} {f' g' : NormTm Γ (X , B)}
                     → norm-pair f f' ≡ norm-pair g g' → f ≡ g
norm-pair-injectiveˡ refl = refl

norm-pair-injectiveʳ : {n : ℕ} {Γ : Con n} {X A B : Ty n}
                       {f g : NormTm Γ (X , A)} {f' g' : NormTm Γ (X , B)}
                     → norm-pair f f' ≡ norm-pair g g' → f' ≡ g'
norm-pair-injectiveʳ refl = refl

------------------------------------------------------------------------
-- denormalize normalize ∼

denormalize-WkNormTmRight∼snd·denormalize : {n : ℕ} {Γ : Con n} {A B C : Ty n} (f : NormTm Γ (B , C)) → denormalize (WkNormTmRight {A = A} f) ∼ snd · (denormalize f)
denormalize-WkNormTmRight∼snd·denormalize (norm-proj x) = ∼refl
denormalize-WkNormTmRight∼snd·denormalize (norm-comp f k x) = ∼trans (∼· (denormalize-WkNormTmRight∼snd·denormalize f) ∼refl) (assoc snd (denormalize f) (var k · norm-proj→Tm x))
denormalize-WkNormTmRight∼snd·denormalize norm-term = ∼sym (text (snd · term))
denormalize-WkNormTmRight∼snd·denormalize (norm-pair f g) = ∼trans (∼pair (denormalize-WkNormTmRight∼snd·denormalize f) (denormalize-WkNormTmRight∼snd·denormalize g))
                                                                   (∼sym (pnat snd (denormalize f) (denormalize g)))

denormalize-WkNormTmLeft∼fst·denormalize : {n : ℕ} {Γ : Con n} {A B C : Ty n} (f : NormTm Γ (A , C)) → denormalize (WkNormTmLeft {B = B} f) ∼ fst · (denormalize f)
denormalize-WkNormTmLeft∼fst·denormalize (norm-proj x) = ∼refl
denormalize-WkNormTmLeft∼fst·denormalize (norm-comp f k x) = ∼trans (∼· (denormalize-WkNormTmLeft∼fst·denormalize f) ∼refl) (assoc fst (denormalize f) (var k · norm-proj→Tm x))
denormalize-WkNormTmLeft∼fst·denormalize norm-term = ∼sym (text (fst · term))
denormalize-WkNormTmLeft∼fst·denormalize (norm-pair f g) = ∼trans (∼pair (denormalize-WkNormTmLeft∼fst·denormalize f) (denormalize-WkNormTmLeft∼fst·denormalize g))
                                                                  (∼sym (pnat fst (denormalize f) (denormalize g)))

denormalize-norm-id∼id : {n : ℕ} {Γ : Con n} {A : Ty n} → _∼_ {Γ = Γ} (denormalize (norm-id {A = A})) id
denormalize-norm-id∼id {A = X x} = ∼refl
denormalize-norm-id∼id {A = 𝟙} = ∼sym (text id)
denormalize-norm-id∼id {A = A × B} = ∼trans (∼pair (∼trans (denormalize-WkNormTmLeft∼fst·denormalize norm-id) (∼trans (∼· ∼refl denormalize-norm-id∼id) (unitr fst)))
                                                   (∼trans (denormalize-WkNormTmRight∼snd·denormalize norm-id) (∼trans (∼· ∼refl denormalize-norm-id∼id) (unitr snd))))
                                            pext

denormalize-norm-fst∼fst : {n : ℕ} {Γ : Con n} {A B : Ty n} → _∼_ {Γ = Γ} (denormalize (norm-fst {A = A} {B = B})) fst
denormalize-norm-fst∼fst = ∼trans (denormalize-WkNormTmLeft∼fst·denormalize norm-id) (∼trans (∼· ∼refl denormalize-norm-id∼id) (unitr fst))

denormalize-norm-snd∼snd : {n : ℕ} {Γ : Con n} {A B : Ty n} → _∼_ {Γ = Γ} (denormalize (norm-snd {A = A} {B = B})) snd
denormalize-norm-snd∼snd = ∼trans (denormalize-WkNormTmRight∼snd·denormalize norm-id) (∼trans (∼· ∼refl denormalize-norm-id∼id) (unitr snd))

-- proposition : ∀ t, (denormalize (normalize t)) ∼ t
denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A : Arr n} (f : Tm Γ A) → denormalize (normalize f) ∼ f
denormalize-normalize∼ f = {!!}
-- denormalize-normalize∼ (var x) = {!!}
-- denormalize-normalize∼ id = denormalize-norm-id∼id
-- denormalize-normalize∼ term = ∼refl
-- denormalize-normalize∼ (pair f g) = ∼pair (denormalize-normalize∼ f) (denormalize-normalize∼ g)
-- denormalize-normalize∼ fst = denormalize-norm-fst∼fst
-- denormalize-normalize∼ snd = denormalize-norm-snd∼snd
-- denormalize-normalize∼ (f · g) = ∼trans (lem-denormalize-normalize∼ (normalize f) (normalize g)) (∼· (denormalize-normalize∼ f) (denormalize-normalize∼ g))
--   where
--   lem-denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A B C : Ty n} (f : NormTm Γ (A , B)) (g : NormTm Γ (B , C)) → denormalize (merge-NormTm f g) ∼ (denormalize f) · (denormalize g)
--   lem-denormalize-normalize∼ (norm-proj x) (norm-proj here) = ∼sym (unitr (norm-proj→Tm x))
--   lem-denormalize-normalize∼ (norm-comp f k x) (norm-proj here) = ∼sym (unitr (denormalize f · (var k · norm-proj→Tm x)))
--   lem-denormalize-normalize∼ (norm-pair f g) (norm-proj (►-left x)) = ∼trans (∼trans (lem-denormalize-normalize∼ f (norm-proj x))
--                                                                                    (∼· (∼sym (pfst (denormalize f) (denormalize g))) ∼refl))
--                                                                            (assoc (pair (denormalize f) (denormalize g)) fst (norm-proj→Tm x))
--   lem-denormalize-normalize∼ (norm-pair f g) (norm-proj (►-right x)) = ∼trans (∼trans (lem-denormalize-normalize∼ g (norm-proj x))
--                                                                                     (∼· (∼sym (psnd (denormalize f) (denormalize g))) ∼refl))
--                                                                             (assoc (pair (denormalize f) (denormalize g)) snd (norm-proj→Tm x))
--   lem-denormalize-normalize∼ f (norm-comp g k x) = {!!}
--   lem-denormalize-normalize∼ f norm-term = ∼trans (text (denormalize (merge-NormTm f norm-term))) (∼sym (text (denormalize f · term)))
--   lem-denormalize-normalize∼ f (norm-pair g h) = ∼trans {!!} (∼sym (pnat (denormalize f) (denormalize g) (denormalize h)))

------------------------------------------------------------------------
-- NormTm constructors injectivity

≡NormTm→∼Tm : {n : ℕ} {Γ : Con n} {A : Arr n} (t u : Tm Γ A) → (normalize t ≡ normalize u) → t ∼ u
≡NormTm→∼Tm t u eq = ∼trans (∼sym (denormalize-normalize∼ t)) (∼trans (≡→∼ (cong denormalize eq)) (denormalize-normalize∼ u))
