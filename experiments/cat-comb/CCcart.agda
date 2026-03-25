--- Categorical combinators for cartesian categories

open import Prelude
open import Ty

infixl 6 _$_

data Tm {n : ℕ} (Γ : Con n) : Ty n → Type where
  var : {A : Ty n} → A ∈ Γ → Tm Γ A
  _$_ : {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  term : Tm Γ 𝟙
  pair : {A B : Ty n} → Tm Γ A → Tm Γ B → Tm Γ (A × B)
  cfst : {A B : Ty n} → Tm Γ (A × B ⇒ A)
  csnd : {A B : Ty n} → Tm Γ (A × B ⇒ B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Ty n} → Tm Γ A → Tm Γ A → Type where
  fstpair : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → cfst $ pair t u ∼ t
  sndpair : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → csnd $ pair t u ∼ u
  extpair : {A B : Ty n} (t : Tm Γ (A × B)) → pair (cfst $ t) (csnd $ t) ∼ t
  uterm : (t : Tm Γ 𝟙) → t ∼ term

  $abs : {A B : Ty n} (t : Tm (Γ ▹ A) B) (u : Tm Γ A) → abs t $ u ∼ {!!}

  -- unitr : {A B : Ty n} (f : Tm Γ (A ⇒ B)) → f $ id ∼ f
  -- assoc : {A B C D : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (B ⇒ C)) (h : Tm Γ (C ⇒ D)) → (f $ g) $ h ∼ f $ (g $ h)
  -- pfst : {A B C : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (A ⇒ C)) → pair f g $ cfst ∼ f
  -- psnd : {A B C : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (A ⇒ C)) → pair f g $ csnd ∼ g
  -- pnat : {A' A B C : Ty n} (f : Tm Γ (A' ⇒ A)) (g : Tm Γ (A ⇒ B)) (h : Tm Γ (A ⇒ C)) → f $ pair g h ∼ pair (f $ g) (f $ h)
  -- pext : {A B : Ty n} → pair cfst csnd ∼ id {A = A × B}
  -- text : {A : Ty n} (f : Tm Γ 𝟙) → f ∼ term
  -- evabs : {A B : Ty n} (t : Tm (Γ ▹ A) B) (u : Tm Γ A) → {!!} $ app ∼ {!!} -- pair (abs f) g $ app ∼ pair id g $ {!f!}
  -- -- absc : ?
  -- absapp : {A B : Ty n} → abs {!!} ∼ {!!}
  ∼refl : {A : Ty n} {t : Tm Γ A} → t ∼ t
  ∼sym : {A : Ty n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  ∼trans : {A : Ty n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v
