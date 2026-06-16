open import Prelude
open import Ty

-- PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set
-- PS Γ (A , X x) = {!!}
-- PS Γ (A , 𝟙) = Unit
-- PS Γ (A , B × C) = PS Γ (A , B) ∧ PS Γ (A , C)

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  proj : {n : ℕ} {Γ : Con n} {x y : Ty n} → y ► x → PS Γ (x , y)
  comp : {n : ℕ} {Γ : Con n} {x y z : Ty n} → PS Γ (x , y) → (y , z) ∈ Γ → PS Γ (x , z)
  prod : {n : ℕ} {Γ : Con n} {x y z : Ty n} → PS Γ (x , y) → PS Γ (x , z) → PS Γ (x , y × z)
  void : {n : ℕ} {Γ : Con n} {x y : Ty n} → PS Γ (x , y) → PS Γ (x , 𝟙)

-- data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
--   proj : {n : ℕ} {x y : Ty n} → y ► x → PS ε (x , y)
--   comp : {n : ℕ} {Γ : Con n} {x y z : Ty n} → PS Γ (x , y) → PS (Γ ▹ (y , z)) (x , z)
--   prod : {n : ℕ} {Γ Γ': Con n} {x y z : Ty n} → PS Γ (x , y) → PS Γ' (x , z) → tgt(Γ) ∩ tgt(Γ') ≡ ε → PS (Γ ∪ Γ') (x , y × z)
--   void : {n : ℕ} {Γ : Con n} {x y : Ty n} → PS Γ (x , y) → PS Γ (x , 𝟙)

PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
PS⊢X⇒X = proj var

PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 0) , X (# 1))) (X (# 0) , X (# 1))
PSX⇒Y⊢X⇒Y = comp (proj var) here

PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ ((X (# 0)) , (X (# 1))) ▹ (X (# 1) , X (# 2))) (X (# 0) , X (# 2))
PSX⇒Y,Y⇒Z⊢X⇒Z = comp (comp (proj var) (drop here)) here

PS⊢X⇒1 : PS {n = 1} ε (X (# 0) , 𝟙)
PS⊢X⇒1 = void (proj var)

-- not a pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒1⊢X⇒1 : PS {n = 1} (ε ▹ (X (# 0) , 𝟙)) (X (# 0) , 𝟙)
-- PSX⇒1⊢X⇒1 = ?

PS⊢X×Y⇒X : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 0))
PS⊢X×Y⇒X = proj (left var)

PS⊢X×Y⇒Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1))
PS⊢X×Y⇒Y = proj (right var)

PS⊢X×Y⇒X×Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1) × X (# 0))
PS⊢X×Y⇒X×Y = proj reorder

PSX⇒Y,X⇒Z⊢X⇒Y×Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1) × X (# 2))
PSX⇒Y,X⇒Z⊢X⇒Y×Z = prod (comp (proj var) (drop here)) (comp (proj var) here)

PS⊢X×Y⇒Y×X : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1) × X (# 0))
PS⊢X×Y⇒Y×X = proj reorder

-- not pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒Y,X⇒Z⊢X⇒Y : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1))
-- PSX⇒Y,X⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 2))




-- PS⊢X⇒Y⇒X : PS {n = 2} ε (X (# 0) ⇒ X (# 1) ⇒ X (# 0))
-- PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z : PS {n = 3} ε ((X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 2))
-- PSX⊢X : PS {n = 1} (ε ▹ X (# 0)) (X (# 0))
-- PSX,Y⊢X : PS {n = 2} (ε ▹ X (# 0) ▹ X (# 1)) (X (# 0))
-- PSX⇒Y⇒Z,X⇒Y,X⊢Z : PS {n = 3} (ε ▹ (X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 2))
-- PSX⇒Y,X⊢Y : PS {n = 2} (ε ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 1))
-- PS⊢[X⇒Y]⇒X⇒Y : PS {n = 2} ε ((X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 1))
-- PS⊢[X⇒Z]⇒[X⇒Y]⇒[X⇒Z] : PS {n = 3} ε ((X (# 0) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 2))
-- PS⊢[X⇒Z]⇒X⇒Y⇒Z : PS {n = 3} ε ((X (# 0) ⇒ X (# 2)) ⇒ X (# 0) ⇒ X (# 1) ⇒ X (# 2))
-- PS⊢[X⇒Y⇒Z⇒W]⇒[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒W : PS {n = 4} ε ((X (# 0) ⇒ X (# 1) ⇒ X (# 2) ⇒ X (# 3)) ⇒ (X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 3))
