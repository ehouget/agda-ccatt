--- Categorical combinators for cartesian categories
--- (see CC for closure added)

open import Prelude
open import Ty

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  _·_ : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pair : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  cfst : {A B : Ty n} → Tm Γ (A × B , A)
  csnd : {A B : Ty n} → Tm Γ (A × B , B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  fstpair : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · cfst ∼ f
  sndpair : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · csnd ∼ g
  extpair : {X A B : Ty n} (f : Tm Γ (X , A × B)) → pair (f · cfst) (f · csnd) ∼ f
  uterm : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → {!!} ∼ {!!}

  -- -- unitr : {A B : Ty n} (f : Tm Γ (A ⇒ B)) → f $ id ∼ f
  -- -- assoc : {A B C D : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (B ⇒ C)) (h : Tm Γ (C ⇒ D)) → (f $ g) $ h ∼ f $ (g $ h)
  -- -- pfst : {A B C : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (A ⇒ C)) → pair f g $ cfst ∼ f
  -- -- psnd : {A B C : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (A ⇒ C)) → pair f g $ csnd ∼ g
  -- -- pnat : {A' A B C : Ty n} (f : Tm Γ (A' ⇒ A)) (g : Tm Γ (A ⇒ B)) (h : Tm Γ (A ⇒ C)) → f $ pair g h ∼ pair (f $ g) (f $ h)
  -- -- pext : {A B : Ty n} → pair cfst csnd ∼ id {A = A × B}
  -- -- text : {A : Ty n} (f : Tm Γ 𝟙) → f ∼ term
  -- -- evabs : {A B : Ty n} (t : Tm (Γ ▹ A) B) (u : Tm Γ A) → {!!} $ app ∼ {!!} -- pair (abs f) g $ app ∼ pair id g $ {!f!}
  -- -- -- absc : ?
  -- -- absapp : {A B : Ty n} → abs {!!} ∼ {!!}
  -- ∼refl : {A : Ty n} {t : Tm Γ A} → t ∼ t
  -- ∼sym : {A : Ty n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  -- ∼trans : {A : Ty n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v
