open import Prelude
open import Ty

-- PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set
-- PS Γ (A , X x) = {!!}
-- PS Γ (A , 𝟙) = Unit
-- PS Γ (A , B × C) = PS Γ (A , B) ∧ PS Γ (A , C)

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  proj : {n : ℕ} {Γ : Con n} {x y : Ty n} → y ► x → PS Γ (x , y)
  comp : {n : ℕ} {Γ : Con n} {x y z : Ty n} → PS Γ (x , y) →  (y , z) ∈ Γ → PS Γ (x , z)
  prod : {n : ℕ} {Γ : Con n} {x y z : Ty n} → PS Γ (x , y) → PS Γ (x , z) → PS Γ (x , y × z)
  void : {n : ℕ} {Γ : Con n} {x y : Ty n} → PS Γ (x , y) → PS Γ (x , 𝟙)

PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
PS⊢X⇒X = proj here

PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 0) , X (# 1))) (X (# 0) , X (# 1))
PSX⇒Y⊢X⇒Y = comp (proj here) here

PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ ((X (# 0)) , (X (# 1))) ▹ (X (# 1) , X (# 2))) (X (# 0) , X (# 2))
PSX⇒Y,Y⇒Z⊢X⇒Z = comp (comp (proj here) (drop here)) here

PS⊢X⇒1 : PS {n = 1} ε (X (# 0) , 𝟙)
PS⊢X⇒1 = void (proj here)

-- not a pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒1⊢X⇒1 : PS {n = 1} (ε ▹ (X (# 0) , 𝟙)) (X (# 0) , 𝟙)
-- PSX⇒1⊢X⇒1 = ?

PS⊢X×Y⇒X : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 0))
PS⊢X×Y⇒X = proj (left (here))

PS⊢X×Y⇒Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1))
PS⊢X×Y⇒Y = proj (right (here))

PS⊢X×Y⇒X×Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 0) × X (# 1))
PS⊢X×Y⇒X×Y = proj here

PSX⇒Y,X⇒Z⊢X⇒Y×Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1) × X (# 2))
PSX⇒Y,X⇒Z⊢X⇒Y×Z = prod (comp (proj here) (drop here)) (comp (proj here) here)

-- not pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒Y,X⇒Z⊢X⇒Y : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1))
-- PSX⇒Y,X⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 2))
