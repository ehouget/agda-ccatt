--- Categorical combinators for cartesian categories

open import Prelude
open import Ty
open import PS

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  id  : {A : Ty n} → Tm Γ (A , A)
  _·_ : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  unitl  : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr  : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc  : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼·     : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼refl  : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym   : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

WkTmTy : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm (WkCon Γ) (WkTy A , WkTy B)
WkTmTy (var x) = var (Wk∈ x)
WkTmTy id = id
WkTmTy (f · g) = WkTmTy f · WkTmTy g

WkTmTm : {n : ℕ} {Γ : Con n} {A : Arr n} {B : Arr n} → Tm Γ A → Tm (Γ ▹ B) A
WkTmTm (var x) = var (drop x)
WkTmTm id = id
WkTmTm (f · g) = WkTmTm f · WkTmTm g

PSTm : {n : ℕ} {Γ : Con n} {A : Arr n} → PS Γ A → Tm Γ A
PSTm start = id
PSTm (ext ps) = WkTmTm (WkTmTy (PSTm ps)) · var here

≡→∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : Tm Γ A} → t ≡ u → t ∼ u
≡→∼ refl = ∼refl

------ Début contribution Eliott Houget ------

-----------------------------------------------------------------------
-- Proof of PSEq
-----------------------------------------------------------------------

-- definition : sub proof system of term derivation
data NormTm {n : ℕ} (Γ : Con n) : Arr n → Type where
  norm-id : {A : Ty n} → NormTm Γ (A , A)
  _▸_     : {A B C : Ty n} → NormTm Γ (A , B) → (B , C) ∈ Γ → NormTm Γ (A , C)

-- transformation : concatenation of two normal terms
merge-NormTm : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : NormTm Γ (A , B)) (u : NormTm Γ (B , C)) → NormTm Γ (A , C)
merge-NormTm t norm-id = t
merge-NormTm t (u ▸ x) = (merge-NormTm t u) ▸ x

-- proposition : association of the concatenation of two normal terms
merge-NormTm-assoc : {n : ℕ} {Γ : Con n} {A B C D : Ty n} (t : NormTm Γ (A , B)) (u : NormTm Γ (B , C)) (v : NormTm Γ (C , D)) → merge-NormTm t (merge-NormTm u v) ≡ merge-NormTm (merge-NormTm t u) v
merge-NormTm-assoc t u norm-id = refl
merge-NormTm-assoc t u (v ▸ x) = cong (_▸ x) (merge-NormTm-assoc t u v)

-- transformation :Transform a term in its normal form (projection of the proof system on the sub proof system)
normalize : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → NormTm Γ A
normalize (var x)  = norm-id ▸ x
normalize id       = norm-id
normalize (t · t') = merge-NormTm (normalize t) (normalize t')

-- transformation : transform a normal term into a general term (inclusion of the sub proof system in the general proof system)
denormalize : {n : ℕ} {Γ : Con n} {A : Arr n} (t : NormTm Γ A) → Tm Γ A
denormalize norm-id = id
denormalize (t ▸ x) = (denormalize t) · var x

-- proposition : ∀ t, (denormalize (normalize t)) ∼ t
denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → denormalize (normalize t) ∼ t
denormalize-normalize∼ (var x)  = unitl (var x)
denormalize-normalize∼ id       = ∼refl
denormalize-normalize∼ (t · t') = ∼trans (lem-denormalize-normalize∼ (normalize t) (normalize t')) (∼· (denormalize-normalize∼ t) (denormalize-normalize∼ t'))
  where
  lem-denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : NormTm Γ (A , B)) (t' : NormTm Γ (B , C)) → denormalize (merge-NormTm t t') ∼ (denormalize t) · (denormalize t')
  lem-denormalize-normalize∼ t norm-id  = ∼sym (unitr (denormalize t))
  lem-denormalize-normalize∼ t (t' ▸ x) = ∼trans (∼· (lem-denormalize-normalize∼ t t') ∼refl) (assoc (denormalize t) (denormalize t') (var x))

-- proposition : there is no loop in the context of a pasting scheme
no-loop-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Ty n} {eq : x ≡ y} → ¬ ((x , y) ∈ Γ)
no-loop-in-PSCon ps {eq = refl} = lem-no-loop-in-PSCon ps
  where
  lem-no-loop-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {B : Ty n} → ¬ ((B , B) ∈ Γ)
  lem-no-loop-in-PSCon (ext ps) (drop k) = (lem-WkCon-dont-add-loop (lem-no-loop-in-PSCon ps)) k
    where
    lem-WkCon-dont-add-loop : {n : ℕ} {Γ : Con n} {A : Ty (suc n)} → ({B : Ty n} → (¬((B , B) ∈ Γ))) → (¬((A , A) ∈ (WkCon Γ)))
    lem-WkCon-dont-add-loop {Γ = ε ▹ (X x , X x)}               f here     = f here
    lem-WkCon-dont-add-loop {Γ = Γ ▹ (X w , X x) ▹ (X y , X y)} f here     = f here
    lem-WkCon-dont-add-loop {Γ = Γ ▹ (X w , X x) ▹ (X y , X z)} f (drop k) = (lem-WkCon-dont-add-loop (λ t → f (drop t))) k

-- proposition : there is no long arrow to 0 in the context of pasting scheme
no-long-arrow-to-0-in-PSCon : {n : ℕ} {Γ : Con (suc (suc n))} {A : Arr (suc (suc n))} (ps : PS Γ A) {k : Fin n} → ¬((X (suc (suc k)) , (X (# 0))) ∈ Γ)
no-long-arrow-to-0-in-PSCon {suc n} (ext ps) (drop k) = (lem-WkCon-dont-add-long-arrow-to-0 ((no-long-arrow-to-0-in-PSCon ps))) k
  where
  lem-WkCon-dont-add-long-arrow-to-0 : {n : ℕ} {Γ : Con (suc (suc n))}
                                     → ({k : Fin n} → ¬((X (suc (suc k)) , (X (# 0))) ∈ Γ))
                                     → ({k : Fin (suc n)} → ¬((X (suc (suc k)) , (X (# 0))) ∈ (WkCon Γ)))
  lem-WkCon-dont-add-long-arrow-to-0 {Γ = ε ▹ (X x₁ , X y₁)} f (drop ())
  lem-WkCon-dont-add-long-arrow-to-0 {Γ = Γ ▹ (X x₂ , X y₂) ▹ (X x₁ , X y₁)} f (drop k) = (lem-WkCon-dont-add-long-arrow-to-0 (λ x → f (drop x))) k


-- propostion : source of a arrow in a pasting scheme is greater than its target
Arr-in-PSCon-are-forward : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Fin n} → (X x , X y) ∈ Γ → x ≥Fin y
Arr-in-PSCon-are-forward (ext start)    here     = z≤n
Arr-in-PSCon-are-forward (ext (ext ps)) here     = z≤n
Arr-in-PSCon-are-forward (ext (ext ps)) (drop k) = (lem-WkCon-keep-Arr-forward (Arr-in-PSCon-are-forward (ext ps)))  k
  where
  lem-WkCon-keep-Arr-forward : {n : ℕ} {Γ : Con n}
                             → ({x₁ y₁ : Fin n} → (X x₁ , X y₁) ∈ Γ → x₁ ≥Fin y₁)
                             → ({x₂ y₂ : Fin (suc n)} → (X x₂ , X y₂) ∈ WkCon Γ → x₂ ≥Fin y₂)
  lem-WkCon-keep-Arr-forward {Γ = ε ▹ (X i , X j)}        f {x₂ = .(suc i)} {y₂ = .(suc j)} here     = s≤s (f here)
  lem-WkCon-keep-Arr-forward {Γ = Γ ▹ neck ▹ (X i , X j)} f {x₂ = .(suc i)} {y₂ = .(suc j)} here     = s≤s (f here)
  lem-WkCon-keep-Arr-forward {Γ = Γ ▹ neck ▹ (X i , X j)} f {x₂ = x₂}       {y₂ = y₂}       (drop k) = (lem-WkCon-keep-Arr-forward λ l → f (drop l)) k

-- proposition : the source of a normal term is greater than its target
Arr-of-NormTm-in-PSCon-are-forward : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Fin n} → (t : NormTm Γ (X x , X y)) → x ≥Fin y
Arr-of-NormTm-in-PSCon-are-forward start    norm-id             = ≤-refl
Arr-of-NormTm-in-PSCon-are-forward (ext ps) norm-id             = ≤-refl
Arr-of-NormTm-in-PSCon-are-forward (ext ps) (_▸_ {B = X k} t x) = ≤-trans (Arr-in-PSCon-are-forward (ext ps) x) (Arr-of-NormTm-in-PSCon-are-forward (ext ps) t)

-- proposition : if a arrow is contain in a weak context, then it's a weak arrow
Ty∈WkCon→WkTy∈Con : {n : ℕ} {B : Arr (suc n)} {Γ : Con n} → B ∈ (WkCon Γ) → ∃[ A ] (WkArr A ≡ B ∧ A ∈ Γ)
Ty∈WkCon→WkTy∈Con {Γ = ε ▹ head} here = head , refl , here
Ty∈WkCon→WkTy∈Con {Γ = Γ ▹ neck ▹ head} here = head , refl , here
Ty∈WkCon→WkTy∈Con {Γ = Γ ▹ neck ▹ head} (drop k) = proj₁ (Ty∈WkCon→WkTy∈Con k) , proj₁ (proj₂ (Ty∈WkCon→WkTy∈Con k)) , drop (proj₂ (proj₂ (Ty∈WkCon→WkTy∈Con k)))

-- proposition : the WkArr transformation is injective
WkArr-injective : {n : ℕ} {Γ : Con n} {A B : Arr n} → WkArr A ≡ WkArr B → A ≡ B
WkArr-injective {A = X i , X j} {B = X .i , X .j} refl = refl

-- proposition : the application of the drop contructor is injective
drop-injective : {n : ℕ} {Γ : Con n} {A B : Arr n} {x y : A ∈ Γ} → drop {B = B} x ≡ drop {B = B} y → x ≡ y
drop-injective refl = refl

-- transformation : get rid of the weakening at both side of the ∈ sign
WkArr∈WkCon→Arr∈Con : {n : ℕ} {Γ : Con n} {A B : Ty n} → (WkTy A , WkTy B) ∈ WkCon Γ → (A , B) ∈ Γ
WkArr∈WkCon→Arr∈Con {Γ = Γ ▹ (X i , X j)} {A = X .i} {B = X .j} here = here
WkArr∈WkCon→Arr∈Con {Γ = Γ ▹ (X i , X j)} {A = X x} {B = X y} (drop k) = drop (WkArr∈WkCon→Arr∈Con k)

-- propostion : the WkArr∈WkCon→Arr∈Con transformation is injective
WkArr∈WkCon→Arr∈Con-injective : {n : ℕ} {Γ : Con n} {A B : Ty n} {x y : (WkTy A , WkTy B) ∈ WkCon Γ} → WkArr∈WkCon→Arr∈Con x ≡ WkArr∈WkCon→Arr∈Con y → x ≡ y
WkArr∈WkCon→Arr∈Con-injective {Γ = Γ ▹ (X i , X j)} {A = X .i} {B = X .j} {x = here} {y = here} eq = refl
WkArr∈WkCon→Arr∈Con-injective {Γ = Γ ▹ (X i , X j)} {A = X k} {B = X l} {x = drop x} {y = drop y} eq = cong drop (WkArr∈WkCon→Arr∈Con-injective (drop-injective eq))

-- proposition : there is no 0 in the weakening of a context of a pasting scheme
no-0-in-WkPSCon : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {y : Ty (suc n)} → ¬ ((y , X (# 0)) ∈ WkCon Γ)
no-0-in-WkPSCon (ext ps) (drop k) = (lem-WkCon-dont-add-0 (no-0-in-WkPSCon ps)) k
  where
  lem-WkCon-dont-add-0 : {n : ℕ} {Γ : Con n}
                       → ({y : Ty (suc n)} → ¬((y , X (# 0)) ∈ WkCon Γ))
                       → ({y : Ty (suc (suc n))} → ¬((y , X (# 0)) ∈ (WkCon (WkCon Γ))))
  lem-WkCon-dont-add-0 {Γ = ε ▹ (X x₁ , X y₁)} f (drop ())
  lem-WkCon-dont-add-0 {Γ = Γ ▹ (X x₂ , X y₂) ▹ (X x₁ , X y₁)} f (drop k) = (lem-WkCon-dont-add-0 (λ x → f (drop x))) k

-- proposition : each arrow in a pasting scheme context is different of all the other one
no-repetition-in-PSCon' : {n : ℕ} {Γ : Con n} {A B C : Arr n} (ps : PS (Γ ▹ B) A) → C ∈ Γ → B ≢ C
no-repetition-in-PSCon' (ext (ext start)) here ()
no-repetition-in-PSCon' (ext (ext start)) (drop ()) eq
no-repetition-in-PSCon' (ext {Γ = Γ} ps) k eq = contradiction ((subst (λ x → x ∈ WkCon Γ) (sym eq) k)) (no-0-in-WkPSCon ps)

-- proposition : each arrow in a pasting scheme context appears only once
no-repetition-in-PSCon : {n : ℕ} {Γ : Con n} {A B : Arr n} (ps : PS Γ A) (x y : B ∈ Γ) → x ≡ y
no-repetition-in-PSCon ps here here = refl
no-repetition-in-PSCon ps here (drop y) = contradiction refl (no-repetition-in-PSCon' ps y)
no-repetition-in-PSCon ps (drop x) here = contradiction refl (no-repetition-in-PSCon' ps x)
no-repetition-in-PSCon (ext ps) (drop x) (drop y) = cong drop ((lem-WkCon-dont-add-repetition (no-repetition-in-PSCon ps)) x y)
  where
  lem-WkCon-dont-add-repetition : {n : ℕ} {Γ : Con n}
                              → ({B : Arr n} (x₁ y₁ : B ∈ Γ) → x₁ ≡ y₁)
                              → ({B : Arr (suc n)} (x₂ y₂ : B ∈ WkCon Γ) → x₂ ≡ y₂)
  lem-WkCon-dont-add-repetition {Γ = Γ} f {B = B} x₂ y₂ = aux (Ty∈WkCon→WkTy∈Con x₂) (Ty∈WkCon→WkTy∈Con y₂)
    where
    aux : (∃-syntax (λ Ax → WkArr Ax ≡ B ∧ (Ax ∈ Γ))) → (∃-syntax (λ Ay → WkArr Ay ≡ B ∧ (Ay ∈ Γ))) → x₂ ≡ y₂
    aux (ax , refl , zx) (ay , eqy , zy) = aux2 (sym (WkArr-injective {Γ = Γ} eqy))
      where
      aux2 : (eqaxay : ax ≡ ay) → x₂ ≡ y₂
      aux2 refl = WkArr∈WkCon→Arr∈Con-injective (f (WkArr∈WkCon→Arr∈Con x₂) (WkArr∈WkCon→Arr∈Con y₂))

-- proposition :arrows in pasting scheme have the form x_i+1 → x_i
form-of-arrow-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} {x y : Fin n} (ps : PS Γ A) → (X x , X y) ∈ Γ → inject₁ x ≡ suc y
form-of-arrow-in-PSCon {x = zero}        {y = zero}  ps       k        = ⊥-elim (no-loop-in-PSCon ps {eq = refl} k)
form-of-arrow-in-PSCon {x = zero}        {y = suc y} ps       k        = contradiction (Arr-in-PSCon-are-forward ps k) (<⇒≱ (s≤s z≤n))
form-of-arrow-in-PSCon {x = suc zero}    {y = zero}  ps       k        = refl
form-of-arrow-in-PSCon {x = suc (suc x)} {y = zero}  ps       k        = ⊥-elim (no-long-arrow-to-0-in-PSCon ps k)
form-of-arrow-in-PSCon {x = suc x}       {y = suc y} (ext ps) (drop k) = cong suc (form-of-arrow-in-PSCon ps (suc∈WkCon→∈ k))
  where
  suc∈WkCon→∈ : {n : ℕ} {Γ : Con n} {x y : Fin n} → (X (suc x) , X (suc y)) ∈ WkCon Γ → (X x , X y) ∈ Γ
  suc∈WkCon→∈ {Γ = Γ ▹ (X i , X j)} here = here
  suc∈WkCon→∈ {Γ = Γ ▹ (X i , X j)} (drop k) = drop (suc∈WkCon→∈ k)

-- proposition : no arrow in a weak context has X 0 as source
no-arrow-from-0-in-WkCon : {n : ℕ} {Γ : Con n} {B : Ty (suc n)} → ¬((X (# 0) , B) ∈  WkCon Γ)
no-arrow-from-0-in-WkCon {Γ = Γ ▹ (X i , X j)} (drop k) = no-arrow-from-0-in-WkCon k

-- transformation of a weak arrow in a context that has been extend like in pasting scheme definition to its strengthen version
WkArr∈ExtCon→Arr∈Con : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} → (WkTy A , WkTy B) ∈ (WkCon Γ ▹ (X (# 1) , X (# 0))) → (A , B) ∈ Γ
WkArr∈ExtCon→Arr∈Con {Γ = ε} {B = X y} (drop ())
WkArr∈ExtCon→Arr∈Con {Γ = Γ ▹ (X i , X j)} {A = X x} {B = X y} (drop k) = WkArr∈WkCon→Arr∈Con k

-- transformation : transform a normal term which has a weak arrow in a extend context to a normal term. It's like cutting the X₁ → X₀ arrow and substract 1 to all index.
WkNormTm→NormTm : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} (t : NormTm (WkCon Γ ▹ (X (# 1) , X (# 0))) (WkTy A , WkTy B)) → NormTm Γ (A , B)
WkNormTm→NormTm {A = X i} {B = X .i} norm-id = norm-id
WkNormTm→NormTm {A = X i} {B = X j} (_▸_ {B = X zero} t (drop x)) = contradiction x no-arrow-from-0-in-WkCon
WkNormTm→NormTm {A = X i} {B = X j} (_▸_ {B = X (suc k)} t x) = WkNormTm→NormTm t ▸ WkArr∈ExtCon→Arr∈Con x

-- proposition : if two normal terms are equal then their tail are equal
-▸x-injective : {n : ℕ} {Γ : Con n} {A B C : Ty n} {t u : NormTm Γ (A , B)} {x y : (B , C) ∈ Γ} → t ▸ x ≡ u ▸ y → t ≡ u
-▸x-injective refl = refl

-- propostion : the restriction of WkNormTm→NormTm in pasting scheme is injective
WkNormTm→NormTm-injective-in-PS : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} (ps : PS Γ (A , X (# 0))) {t u : NormTm (WkCon Γ ▹ (X (# 1) , X (# 0))) (WkTy A , WkTy B)} → WkNormTm→NormTm t ≡ WkNormTm→NormTm u → t ≡ u
WkNormTm→NormTm-injective-in-PS {A = .(X (# 0))} {B = X zero} start {norm-id} {norm-id} eq = refl
WkNormTm→NormTm-injective-in-PS {A = .(X (# 0))} {B = X zero} start {_} {u ▸ drop ()} _
WkNormTm→NormTm-injective-in-PS {A = .(X (# 0))} {B = X zero} start {t ▸ drop ()} {_} _
WkNormTm→NormTm-injective-in-PS {A = X _} {B = X _} (ext ps) {norm-id} {norm-id} _ = refl
WkNormTm→NormTm-injective-in-PS {A = _} {B = X .(fromℕ< (s≤s (s≤s ≤-refl)))} (ext ps) {norm-id} {_▸_ {B = X zero} u y} eq = ⊥-elim (no-loop-in-PSCon (ext (ext ps) ) {eq = cong (λ x → X x) (≤-antisym (Arr-of-NormTm-in-PSCon-are-forward (ext (ext ps)) u) (Arr-in-PSCon-are-forward (ext (ext ps)) y))} y)
WkNormTm→NormTm-injective-in-PS {A = _} {B = X .(fromℕ< (s≤s (s≤s ≤-refl)))} (ext ps) {_▸_ {B = X zero} t x} {norm-id} eq = ⊥-elim (no-loop-in-PSCon (ext (ext ps) ) {eq = cong (λ x → X x) (≤-antisym (Arr-of-NormTm-in-PSCon-are-forward (ext (ext ps)) t) (Arr-in-PSCon-are-forward (ext (ext ps)) x))} x)
WkNormTm→NormTm-injective-in-PS {B = X j} (ext ps) {_▸_ {B = X zero} t x} {_} _ = contradiction (Arr-in-PSCon-are-forward (ext (ext ps)) x) (<⇒≱ (s≤s z≤n))
WkNormTm→NormTm-injective-in-PS {B = X j} (ext ps) {_} {_▸_ {B = X zero} u y} eq = contradiction (Arr-in-PSCon-are-forward (ext (ext ps)) y) (<⇒≱ (s≤s z≤n))
WkNormTm→NormTm-injective-in-PS {B = X j} (ext ps) {_▸_ {B = X (suc k)} t x} {_▸_ {B = X (suc l)} u y} eq = aux (form-of-arrow-in-PSCon (ext (ext ps)) x) (form-of-arrow-in-PSCon (ext (ext ps)) y)
  where
  aux : (eqk : inject₁ (suc k) ≡ suc (suc j)) (eqlm : inject₁ (suc l) ≡ suc (suc j)) → (t ▸ x) ≡ (u ▸ y)
  aux eqk eql = aux1 (inject₁-injective (trans (suc-injective eqk) (sym (suc-injective eql))))
    where
    aux1 : (eqlk : k ≡ l) → t ▸ x ≡ u ▸ y
    aux1 refl = aux2 (no-repetition-in-PSCon (ext (ext ps)) x y)
      where
      aux2 : (eq : x ≡ y) → t ▸ x ≡ u ▸ y
      aux2 refl = cong (_▸ x) (WkNormTm→NormTm-injective-in-PS (ext ps) (-▸x-injective eq))

-- Important lemma : there is an unique normal term for an arrow in a pasting scheme
lem-PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (t u : NormTm Γ A) → t ≡ u
lem-PSEq start norm-id norm-id = refl
lem-PSEq (ext ps) (_▸_ {B = X zero} t x) _  = ⊥-elim (no-loop-in-PSCon (ext ps) {eq = refl} x)
lem-PSEq (ext ps) _ (_▸_ {B = X zero} u y) = ⊥-elim (no-loop-in-PSCon (ext ps) {eq = refl} y)
lem-PSEq (ext ps) (_▸_ {B = X (suc (suc k))} t x) _ = ⊥-elim (no-long-arrow-to-0-in-PSCon (ext ps) x)
lem-PSEq (ext ps) _ (_▸_ {B = X (suc (suc l))} u y) = ⊥-elim (no-long-arrow-to-0-in-PSCon (ext ps) y)
lem-PSEq (ext ps) (_▸_ {B = X (suc zero)} t x) (_▸_ {B = X (suc zero)} u y) = subst (λ z → t ▸ x ≡ u ▸ z) (no-repetition-in-PSCon (ext ps) x y) (cong (_▸ x) (WkNormTm→NormTm-injective-in-PS ps (lem-PSEq ps (WkNormTm→NormTm t) (WkNormTm→NormTm u))))

-- if two term have the same normalization, then there are similar
≡NormTm→∼Tm : {n : ℕ} {Γ : Con n} {A : Arr n} (t u : Tm Γ A) → (normalize t ≡ normalize u) → t ∼ u
≡NormTm→∼Tm t u eq = ∼trans (∼sym (denormalize-normalize∼ t)) (∼trans (≡→∼ (cong denormalize eq)) (denormalize-normalize∼ u))

-- Theoreme : pasting scheme are contractible
PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (t u : Tm Γ A) → t ∼ u
PSEq ps t u = ≡NormTm→∼Tm t u (lem-PSEq ps (normalize t) (normalize u))

---------------------------------------------------------------------
-- results and transformations not used
---------------------------------------------------------------------

-- proposition :  merge with norm-id at right do nothing
merge-NormTm-norm-id : {n : ℕ} {Γ : Con n} {A : Arr n} (t : NormTm Γ A) → merge-NormTm norm-id t ≡ t
merge-NormTm-norm-id norm-id = refl
merge-NormTm-norm-id (t ▸ x) = cong (_▸ x) (merge-NormTm-norm-id t)

-- proposition : if two terms are similar, then their normal form are equal -not used
∼Tm→≡NormTm : {n : ℕ} {Γ : Con n} {A : Arr n} (f g : Tm Γ A) → f ∼ g → normalize f ≡ normalize g
∼Tm→≡NormTm .(id · g) g (unitl .g) = merge-NormTm-norm-id (normalize g)
∼Tm→≡NormTm .(g · id) g (unitr .g) = refl
∼Tm→≡NormTm .(f · g · h) .(f · (g · h)) (assoc f g h) = sym (merge-NormTm-assoc (normalize f) (normalize g) (normalize h))
∼Tm→≡NormTm .(f · g) .(f' · g') (∼· {f = f} {f' = f'} {g = g} {g' = g'} sim₁ sim₂) = subst (λ z → merge-NormTm (normalize f) (normalize g) ≡ merge-NormTm z (normalize g')) (∼Tm→≡NormTm f f' sim₁) (subst (λ z → merge-NormTm (normalize f) (normalize g) ≡ merge-NormTm (normalize f) z) (∼Tm→≡NormTm g g' sim₂) refl)
∼Tm→≡NormTm f .f ∼refl = refl
∼Tm→≡NormTm f g (∼sym sim) = sym (∼Tm→≡NormTm g f sim)
∼Tm→≡NormTm f h (∼trans {g = g} sim₁ sim₂) = trans (∼Tm→≡NormTm f g sim₁) (∼Tm→≡NormTm g h sim₂)

-- proposition : normalize and then denormalize the result is the same as doing nothing -not used
normalize-denormalize≡id : {n : ℕ} {Γ : Con n} {A : Arr n} (t : NormTm Γ A) → normalize (denormalize t) ≡ t
normalize-denormalize≡id norm-id = refl
normalize-denormalize≡id (t ▸ x) = cong (_▸ x) (normalize-denormalize≡id t)

-- proposition : if two normal terms are equal, then their denormalize form are similar -not used
≡NormTm→∼denormTm : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : NormTm Γ A} → t ≡ u → (denormalize t ∼ denormalize u)
≡NormTm→∼denormTm refl = ∼refl

------ Fin contribution Eliott ------





-- Substitutions
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub _ Γ ε = Unit
Sub τ Γ (Γ' ▹ (A , B)) = Sub τ Γ Γ' ∧ Tm Γ (A [ τ ]' , B [ τ ]')

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substitution
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A B : Ty n'} → Tm Γ' (A , B) → {τ : SubTy n n'} (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')
var here [ σ , t ] = t
var (drop x) [ σ , t ] = var x [ σ ]
id [ σ ] = id
(f · g) [ σ ] = f [ σ ] · g [ σ ]

-- Equivalence of substitutions
_∼Sub_ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ σ' : Sub τ Γ Γ') → Type
_∼Sub_ {Γ' = ε} tt tt = Unit
_∼Sub_ {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (σ ∼Sub σ') ∧ (t ∼ t')

∼SubRefl : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → σ ∼Sub σ
∼SubRefl {Γ' = ε} σ = tt
∼SubRefl {Γ' = Γ' ▹ A} (σ , t) = ∼SubRefl σ , ∼refl

∼SubSym : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → σ' ∼Sub σ
∼SubSym {Γ' = ε} tt = tt
∼SubSym {Γ' = Γ' ▹ A} (p , q) = ∼SubSym p , ∼sym q

_[_]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ∼ u → σ ∼Sub σ' → t [ σ ] ∼ u [ σ' ]
unitl f [ q ]∼ = ∼trans (unitl (f [ _ ])) (∼refl {f = f} [ q ]∼)
unitr f [ q ]∼ = ∼trans (unitr (f [ _ ])) (∼refl {f = f} [ q ]∼)
assoc f g h [ q ]∼ = ∼trans (assoc (f [ _ ]) (g [ _ ]) (h [ _ ])) (∼· (∼refl {f = f} [ q ]∼) (∼· (∼refl {f = g} [ q ]∼) (∼refl {f = h} [ q ]∼)))
∼· p p' [ q ]∼ = ∼· (p [ q ]∼) (p' [ q ]∼)
∼refl {f = f} [ q ]∼ = lem f q
  where
  lem : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
  lem (var here) (σ , p) = p
  lem (var (drop x)) (σ , p) = lem (var x) σ
  lem id p = ∼refl
  lem (f · g) p = ∼· (∼refl {f = f} [ p ]∼) (∼refl {f = g} [ p ]∼)
∼sym p [ q ]∼ = ∼sym (p [ ∼SubSym q ]∼)
∼trans p p' [ q ]∼ = ∼trans (p [ q ]∼) (p' [ ∼SubRefl _ ]∼)

-- Composition of substitutions
_∘_ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → Sub τ' Γ' Γ'' → Sub τ Γ Γ' → Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} σ' σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t') σ = (σ' ∘ σ) , (t' [ σ ])

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Arr n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (t : Tm Γ'' A) (σ' : Sub τ' Γ' Γ'') (σ : Sub τ Γ Γ') → t [ σ' ] [ σ ] ≡ t [ σ' ∘ σ ]
[∘] (var here) (σ' , f) σ = refl
[∘] (var (drop x)) (σ' , f) σ = [∘] (var x) σ' σ
[∘] id σ' σ = refl
[∘] (f · g) σ' σ = cong₂ _·_ ([∘] f σ' σ) ([∘] g σ' σ)
