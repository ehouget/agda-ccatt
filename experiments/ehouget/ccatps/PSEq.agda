------------------------------------------------------------------------
-- Pasting Schemes for cartesian categories
--
-- A pasting scheme is inhabited by at most one term
------------------------------------------------------------------------

open import Ty
open import Con
open import Tm
open import PS
open import NormTm
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)
open import Prelude

--------------------------------------------------------------------------------
-- WkNormTm⁻¹ restriction to pasting scheme normal term is injective

-- mutual
--   WkNormTm⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {m : Fin n}
--                (f : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc m)))
--              → NormTm Γ (A , X m)
--   WkNormTm⁻¹ (norm-proj x) = norm-proj (Wk►⁻¹ x)
--   WkNormTm⁻¹ (norm-comp f (∈-here refl) (►-here ()))
--   WkNormTm⁻¹ {Γ = Γ ▹ (A , B)} (norm-comp {B = B'} {C = X .(suc _)} f (∈-drop k) (►-here refl)) = norm-comp (WkNormTm⁻¹-aux {!!}) {!!} {!!}
--   WkNormTm⁻¹ (norm-comp {B = B'} {C = C' × C''} f (∈-drop k) x) = norm-comp (WkNormTm⁻¹-aux {!!}) {!!} {!!}
--     -- where
--     -- lem-WkNormTm⁻¹ : {Γ' : Con (suc n)} {A' B' : Ty (suc n)} {m' : Fin (suc n)}
--     --                  (ps' : PS (Γ' ▹ (B' , X (# 0))) (A' , X m'))
--     --                  (f' : NormTm (Γ' ▹ (B' , X (# 0))) (A' , X m'))
--     --                  (eqΓ : Γ' ≡ WkCon Γ) (eqA : A' ≡ WkTy A) (eqB : B' ≡ WkTy B) (eqk : m' ≡ suc m)
--     --                → NormTm Γ (A , X m)
--     -- lem-WkNormTm⁻¹ (ps-weak ps') (norm-proj x) eqΓ eqA eqB eqk = norm-proj {!!}
--     -- lem-WkNormTm⁻¹ (ps-weak ps') (norm-comp f x x₁) eqΓ eqA eqB eqk = {!!}

--   WkNormTm⁻¹-aux : {n : ℕ} {Γ : Con n} {A B C : Ty n} (f : NormTm (WkCon Γ ▹ (WkTy C , X (# 0))) (WkTy A , WkTy B)) → NormTm Γ (A , B)
--   WkNormTm⁻¹-aux {B = X m} (norm-proj x) = norm-proj {!!}
--   WkNormTm⁻¹-aux {B = X m} (norm-comp f k x) = norm-comp {!!} {!!} {!!}
--   WkNormTm⁻¹-aux {B = 𝟙} norm-term = norm-term
--   WkNormTm⁻¹-aux {B = _ × _} (norm-pair f f') = norm-pair (WkNormTm⁻¹-aux f) (WkNormTm⁻¹-aux f')
-- -- WkNormTm⁻¹-aux (norm-proj {k = zero} x) = {!!}
--   -- WkNormTm⁻¹-aux (norm-proj {k = suc k} x) = {!!}
--   -- WkNormTm⁻¹-aux (norm-comp f l x) = {!!}
--   -- WkNormTm⁻¹-aux norm-term = norm-term
--   -- WkNormTm⁻¹-aux (norm-pair f f') = norm-pair (WkNormTm⁻¹-aux f) (WkNormTm⁻¹-aux f')

-- WkNormTm-WkNormTm⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n}
--                              → (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
--                              → (f : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
--                              → WkNormTm (WkNormTm⁻¹ f) ≡ f
-- WkNormTm-WkNormTm⁻¹ {n} {Γ} {A} {B} {k} ps f = lem-WkNormTm-WkNormTm⁻¹ ps f refl refl refl
--   where
--   lem-WkNormTm-WkNormTm⁻¹ : {Γ' : Con (suc n)} {A' : Ty (suc n)}
--                           → (ps' : PS Γ' (A' , X (suc k)))
--                           → (f' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , WkTy (X k)))
--                           → (eqΓ : Γ' ≡ WkCon Γ ▹ (WkTy B , X (# 0)))
--                           → (eqA : A' ≡ WkTy A)
--                           → (eqf : f ≡ f')
--                           → WkNormTm (WkNormTm⁻¹ f) ≡ f
--   lem-WkNormTm-WkNormTm⁻¹ (ps-weak ps') (norm-proj x) eqΓ eqA refl = cong norm-proj Wk►-Wk►⁻¹
--   lem-WkNormTm-WkNormTm⁻¹ (ps-weak ps') (norm-comp f' (∈-here refl) (►-here ())) eqΓ eqA refl
--   lem-WkNormTm-WkNormTm⁻¹ (ps-weak {Γ = Γps} {A = Aps} {B = Bps} ps')
--                           (norm-comp {B = Bcomp} {C = Ccomp} f' l x)
--                           eqΓ eqA refl = lem-eq-WkNormTm-WkNormTm⁻¹ (WkCon-injective (▹-injectiveˡ eqΓ))
--                                                                      (WkTy-injective eqA)
--                                                                      (WkTy-injective (,-injectiveˡ (▹-injectiveʳ eqΓ)))
--     where
--     lem-eq-WkNormTm-WkNormTm⁻¹ : Γps ≡ Γ → Aps ≡ A → Bps ≡ B
--                                 → WkNormTm (WkNormTm⁻¹ f) ≡ f
--     lem-eq-WkNormTm-WkNormTm⁻¹ refl refl refl = {!!} -- lem-lem-WkNormTm-WkNormTm⁻¹ {!!} {!!} {!!} (∈WkCon→∃WkSrc∈WkCon ) {!!} {!!}
--       where
--       lem-lem-WkNormTm-WkNormTm⁻¹ : (∃[ m ] (Ccomp ≡ X m)) → (x' : Ccomp ► suc k) → (eqx : x' ≡ x)
--                                   → (∃[ A' ] (Bcomp ≡ WkTy A'))
--                                   → (l' : {!!}) → (eql : l' ≡ l)
--                                   → (f'' : {!!}) → (eqf' : f'' ≡ f')
--                                   → WkNormTm (WkNormTm⁻¹ f) ≡ f
--       lem-lem-WkNormTm-WkNormTm⁻¹ (.(suc k) , refl) (►-here refl) refl (X x , refl) (∈-drop l') refl = {!!}
--       lem-lem-WkNormTm-WkNormTm⁻¹ (.(suc k) , refl) (►-here refl) refl (𝟙 , refl) (∈-drop l') refl norm-term refl = {!refl!}
--       lem-lem-WkNormTm-WkNormTm⁻¹ (.(suc k) , refl) (►-here refl) refl (fst₁ × fst₂ , refl) (∈-drop l') refl = {!!}


-- test : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n}
--                              → (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
--                              → (f g : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
--                              → WkNormTm⁻¹ f ≡ WkNormTm⁻¹ g → f ≡ g
-- test ps f g eq = trans (sym (WkNormTm-WkNormTm⁻¹ ps f)) (trans (cong WkNormTm eq) (WkNormTm-WkNormTm⁻¹ ps g))

mutual

  WkNormTm⁻¹-injective-in-PS : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n}
                             → (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
                             → (f g : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
                             → WkNormTm⁻¹ f ≡ WkNormTm⁻¹ {!!} → f ≡ g
  WkNormTm⁻¹-injective-in-PS {n} {Γ} {A} {B} {k} ps f g eq = lem-WkNormTm⁻¹-injective-in-PS refl refl refl refl ps f g refl refl
    where
    lem-WkNormTm⁻¹-injective-in-PS : {Γ' : Con (suc n)} {A' B' C' : Ty (suc n)}
                                   → (eqA : A' ≡ WkTy A)
                                   → (eqB : B' ≡ WkTy B)
                                   → (eqC : C' ≡ X (suc k))
                                   → (eqΓ : Γ' ≡ WkCon Γ ▹ (B' , X (# 0)))
                                   → (ps' : PS Γ' (A' , C'))
                                   → (f' g' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , WkTy (X k)))
                                   → (eqf : f ≡ f')
                                   → (eqg : g ≡ g')
                                   → f' ≡ g'
    lem-WkNormTm⁻¹-injective-in-PS eqA eqB eqC eqΓ (ps-weak ps') (norm-proj x) (norm-proj y) refl refl = {!!} -- cong norm-proj (Wk►⁻¹-injective (norm-proj-injective eq))
    lem-WkNormTm⁻¹-injective-in-PS eqA eqB eqC eqΓ (ps-weak ps') _ (norm-comp g' (∈-here refl) (►-here ())) _ _
    lem-WkNormTm⁻¹-injective-in-PS eqA eqB eqC eqΓ (ps-weak ps') (norm-comp f' (∈-here refl) (►-here ())) _ _ _
    lem-WkNormTm⁻¹-injective-in-PS eqA eqB eqC eqΓ (ps-weak ps') (norm-proj x) (norm-comp {C = C} g' l y) refl refl = lem-lem-WkNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple ps l) y refl
      where
      lem-lem-WkNormTm⁻¹-injective-in-PS : (∃[ m ] (C ≡ X m)) → (y' : C ► suc k) → (eqy : y' ≡ y) → f ≡ g
      lem-lem-WkNormTm⁻¹-injective-in-PS (.(suc k) , refl) (►-here refl) eqy = contradiction (x , l) (producer-unicity {ps = ps})
    lem-WkNormTm⁻¹-injective-in-PS eqA eqB eqC eqΓ (ps-weak ps') (norm-comp {C = C} f' l x) (norm-proj y) refl refl = lem-lem-WkNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple ps l) x refl
      where
      lem-lem-WkNormTm⁻¹-injective-in-PS : (∃[ m ] (C ≡ X m)) → (x' : C ► suc k) → (eqx : x' ≡ x) → f ≡ g
      lem-lem-WkNormTm⁻¹-injective-in-PS (.(suc k) , refl) (►-here refl) eqy = contradiction (y , l) (producer-unicity {ps = ps})
    lem-WkNormTm⁻¹-injective-in-PS eqA refl refl eqΓ
                                   (ps-weak {Γ = Γ'} {A = A'} {B = B'} ps')
                                   (norm-comp {B = Bf} {C = Cf} f' lf x) (norm-comp {B = Bg} {C = Cg} g' lg y)
                                   refl refl = lem-tgt (ps-con-tgt-are-simple ps lf) x refl
                                                           (ps-con-tgt-are-simple ps lg) y refl
      where
      lem-tgt : (∃[ mx ] (Cf ≡ X mx)) → (x' : Cf ► suc k) → (eqx : x' ≡ x)
              → (∃[ my ] (Cg ≡ X my)) → (y' : Cg ► suc k) → (eqy : y' ≡ y)
              → f ≡ g
      lem-tgt (.(suc k) , refl) (►-here refl) refl
              (.(suc k) , refl) (►-here refl) refl = lem-src (no-src-repetition-in-PSCon ps lf lg)
        where
        lem-src : Bf ≡ Bg → norm-comp f' lf (►-here refl) ≡ norm-comp g' lg (►-here refl)
        lem-src refl = lem-∈ (no-repetition-in-PSCon ps lf lg) lf refl Γ refl
          where
          lem-∈ : lf ≡ lg → (lf' : (Bf , X (suc k)) ∈ (WkCon Γ ▹ (WkTy B , X (# 0)))) → (eqlf : lf' ≡ lf)
                → (Γ'' : Con n) → (eqΓ' : Γ'' ≡ Γ)
                → norm-comp f' lf (►-here refl) ≡ norm-comp g' lg (►-here refl)
          lem-∈ refl (∈-drop (∈-here x)) refl (Γ'' ▹ (src , tgt)) refl = {!!}
          lem-∈ refl (∈-drop (∈-drop lf')) refl (Γ'' ▹ (src , tgt)) refl = {!!}
-- cong (λ h → norm-comp h lf (►-here refl)) (lem-lem-WkNormTm⁻¹-injective-in-PS f' g' refl refl (∈WkCon→∃WkSrc∈WkCon lf'))
--             where
--             lem-lem-WkNormTm⁻¹-injective-in-PS : (f'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bf))
--                                                → (g'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bf))
--                                                → (eqf' : f'' ≡ f') → (eqg' : g'' ≡ g')
--                                                → (∃[ Bf' ] (Bf ≡ WkTy Bf'))
--                                                → f' ≡ g'
--             lem-lem-WkNormTm⁻¹-injective-in-PS f'' g'' refl refl (X x , refl) = lem- eq
--               where
--               lem- : {!!} → {!!}
--               lem- truc = {!truc!}
--             lem-lem-WkNormTm⁻¹-injective-in-PS norm-term norm-term refl refl (𝟙 , refl) = refl
--             lem-lem-WkNormTm⁻¹-injective-in-PS (norm-pair f'' f''') (norm-pair g'' g''') refl refl (Bf' × Bf'' , refl) = cong₂ norm-pair (WkNormTm⁻¹-aux-injective-in-PS {!!} f'' g'' {!!}) ((WkNormTm⁻¹-aux-injective-in-PS {!!} f''' g''' {!!}))


    --                                       → (B'' : Ty n) → (eqB' : B'' ≡ B)
    --                                       → (eqΓ' : Γ' ≡ Γ)
    --                                       → (eqA' : A' ≡ A)
    --                                       → (eqB' : B' ≡ B)
    --                                       → (ps'' : PS Γ' (A' , X k))
    --                                       → (eqps' : ps'' ≡ ps')
    --                                       → f ≡ g
    --   lem-lem-extNormTm⁻¹-injective-in-PS (.(suc k) , refl) (►-here refl) refl
    --                                       (.(suc k) , refl) (►-here refl) refl
    --                                       (∈-drop lf') refl (∈-drop lg') refl
    --                                       f'' g'' refl refl
    --                                       B'' refl refl refl refl ps'' refl = let eqB : Bf ≡ Bg
    --                                                                               eqB = no-src-repetition-in-PSCon ps lf lg
    --                                                                           in {!no-repetition-in-PSCon ps lf lg!}
    -- --   -- x = y because there are just ∈-here refl
    --   -- k = l because each simple type has an only producer in a pasting scheme context
    --   -- then use eq to conclude

  WkNormTm⁻¹-aux-injective-in-PS : {n : ℕ} {Γ : Con n} {A B C : Ty n}
                                 → (ps : PS Γ (A , B))
                                 → (f g : NormTm (WkCon Γ ▹ (WkTy C , X (# 0))) (WkTy A , WkTy B))
                                 → WkNormTm⁻¹-aux f ≡ WkNormTm⁻¹-aux g → f ≡ g
  WkNormTm⁻¹-aux-injective-in-PS {B = 𝟙} ps norm-term norm-term x = refl
  WkNormTm⁻¹-aux-injective-in-PS {B = X _} ps (norm-proj x) (norm-proj y) eq = {!!} -- cong norm-proj (Wk►⁻¹-injective (norm-proj-injective eq))
  WkNormTm⁻¹-aux-injective-in-PS {B = X i} ps (norm-proj x) (norm-comp {C = C} g l y) eq = lem-lem-WkNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple (ps-weak ps) l) y refl
    where
    lem-lem-WkNormTm⁻¹-injective-in-PS : (∃[ m ] (C ≡ X m)) → (y' : C ► suc i) → (eqy : y' ≡ y) → (norm-proj x) ≡ (norm-comp {C = C} g l y)
    lem-lem-WkNormTm⁻¹-injective-in-PS (.(suc i) , refl) (►-here refl) eqy = contradiction (x , l) (producer-unicity {ps = ps-weak ps})
  WkNormTm⁻¹-aux-injective-in-PS {B = X i} ps (norm-comp {C = C} f k x) (norm-proj y) eq = lem-lem-WkNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple (ps-weak ps) k) x refl
    where
    lem-lem-WkNormTm⁻¹-injective-in-PS : (∃[ m ] (C ≡ X m)) → (x' : C ► suc i) → (eqx : x' ≡ x) → (norm-comp {C = C} f k x) ≡ (norm-proj y)
    lem-lem-WkNormTm⁻¹-injective-in-PS (.(suc i) , refl) (►-here refl) eqy = contradiction (y , k) (producer-unicity {ps = ps-weak ps})
  WkNormTm⁻¹-aux-injective-in-PS {B = X _} ps (norm-comp f k x) (norm-comp g l y) eq = {!!} -- WkNormTm⁻¹-injective-in-PS (ps-weak ps) (norm-comp f k x) (norm-comp g l y) eq
  WkNormTm⁻¹-aux-injective-in-PS {B = _ × _} (ps-pair ps ps') (norm-pair f f') (norm-pair g g') eq = cong₂ norm-pair (WkNormTm⁻¹-aux-injective-in-PS ps f g (norm-pair-injectiveˡ eq))
                                                                                                                     (WkNormTm⁻¹-aux-injective-in-PS ps' f' g' (norm-pair-injectiveʳ eq))

--------------------------------------------------------------------------------
-- extNormTm⁻¹ restriction to pasting scheme normal term is injective

extNormTm⁻¹-injective-in-PS : {n : ℕ} {Γ : Con n} {A B : Ty n}
                              (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0)))
                              (f g : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0)))
                            → extNormTm⁻¹ f ≡ extNormTm⁻¹ g → f ≡ g
extNormTm⁻¹-injective-in-PS {n} {Γ} {A} {B} ps f g eq = lem-extNormTm⁻¹-injective-in-PS refl refl refl ps f g refl refl eq refl
  where
  lem-extNormTm⁻¹-injective-in-PS : {Γ' : Con (suc n)} {A' B' : Ty (suc n)}
                                  → (eqA : A' ≡ WkTy A)
                                  → (eqB : B' ≡ WkTy B)
                                  → (eqΓ : Γ' ≡ WkCon Γ ▹ (B' , X (# 0)))
                                  → (ps' : PS Γ' (A' , X (# 0)))
                                  → (f' g' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0)))
                                  → (eqf : f ≡ f')
                                  → (eqg : g ≡ g')
                                  → (eq' : extNormTm⁻¹ f ≡ extNormTm⁻¹ g)
                                  → (eqeq : eq' ≡ eq)
                                  → f' ≡ g'
  lem-extNormTm⁻¹-injective-in-PS eqA eqB eqΓ (ps-ext ps') (norm-proj x) _ _ _ = contradiction x no-0-in-WkTy
  lem-extNormTm⁻¹-injective-in-PS eqA eqB eqΓ (ps-ext ps') _ (norm-proj y) _ _ = contradiction y no-0-in-WkTy
  lem-extNormTm⁻¹-injective-in-PS eqA refl eqΓ (ps-ext {Γ = Γ'} {A = A'} {B = B'} ps')
                                  (norm-comp {B = Bf} {C = Cf} f' k x) (norm-comp {B = Bg} {C = Cg} g' l y)
                                  refl refl eq' refl = lem-lem-extNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple ps k) x refl
                                                                                           (ps-con-tgt-are-simple ps l) y refl
                                                                                           k refl l refl f' g' refl refl B refl
                                                                                           (WkCon-injective (▹-injectiveˡ eqΓ))
                                                                                           (WkTy-injective eqA)
                                                                                           (WkTy-injective (,-injectiveˡ (▹-injectiveʳ eqΓ)))
                                                                                           ps' refl
    where
    lem-lem-extNormTm⁻¹-injective-in-PS : (∃[ mx ] (Cf ≡ X mx)) → (x' : Cf ► # 0) → (eqx : x' ≡ x)
                                        → (∃[ my ] (Cg ≡ X my)) → (y' : Cg ► # 0) → (eqy : y' ≡ y)
                                        → (k' : (Bf , Cf) ∈ (WkCon Γ ▹ (WkTy B , X (# 0)))) → (eqk : k' ≡ k)
                                        → (l' : (Bg , Cg) ∈ (WkCon Γ ▹ (WkTy B , X (# 0)))) → (eql : l' ≡ l)
                                        → (f'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bf))
                                        → (g'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bg))
                                        → (eqf' : f'' ≡ f')
                                        → (eqg' : g'' ≡ g')
                                        → (B'' : Ty n) → (eqB' : B'' ≡ B)
                                        → (eqΓ' : Γ' ≡ Γ)
                                        → (eqA' : A' ≡ A)
                                        → (eqB' : B' ≡ B)
                                        → (ps'' : PS Γ' (A' , B'))
                                        → (eqps' : ps'' ≡ ps')
                                        → f ≡ g
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-here refl) refl (∈-here refl) refl f'' g'' eqf' eqg' (X x) refl refl refl refl _ _ =  {!!} -- cong (λ h → norm-comp h (∈-here refl) (►-here refl)) (WkNormTm⁻¹-injective-in-PS (ps-weak ps') f' g' eq)
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-here refl) refl (∈-here refl) refl norm-term norm-term refl refl 𝟙 refl _ _ _ _ _ = refl
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-here refl) refl (∈-here refl) refl (norm-pair f'' f''') (norm-pair g'' g''') refl refl (B'' × B''') refl refl refl refl (ps-pair ps'' ps''') refl = cong₂ (λ h h' → norm-comp (norm-pair h h') (∈-here refl) (►-here refl)) (WkNormTm⁻¹-aux-injective-in-PS ps'' f'' g'' (norm-pair-injectiveˡ eq)) (WkNormTm⁻¹-aux-injective-in-PS ps''' f''' g''' (norm-pair-injectiveʳ eq))
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-here x) eqk (∈-drop l') eql _ _ _ _ _ _ _ _ _ = contradiction l' no-0-in-WkCon
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-drop k') eqk l' eql _ _ _ _ _ _ _ _ _ = contradiction k' no-0-in-WkCon
  --   -- x = y because there are just ∈-here refl
  --   -- k = l because each simple type has an only producer in a pasting scheme context
  --   -- then use eq to conclude

  lem-extNormTm⁻¹-injective-in-PS eqA eqB eqΓ (ps-const ps') (norm-proj x) _ _ _ = contradiction x no-0-in-WkTy
  lem-extNormTm⁻¹-injective-in-PS eqA eqB eqΓ (ps-const ps') _ (norm-proj y) _ _ = contradiction y no-0-in-WkTy
  lem-extNormTm⁻¹-injective-in-PS eqA refl eqΓ (ps-const {B = Bps} ps')
                                  (norm-comp {B = Bf} {C = Cf} f' k x) (norm-comp {B = Bg} {C = Cg} g' l y)
                                  refl refl eq' refl = lem-lem-extNormTm⁻¹-injective-in-PS (ps-con-tgt-are-simple ps k) x refl
                                                                                  (ps-con-tgt-are-simple ps l) y refl
                                                                                  k refl
                                                                                  l refl
                                                                                  f' g' refl refl
                                                                                  (WkTy-injective (,-injectiveˡ (▹-injectiveʳ eqΓ)))
    where
    lem-lem-extNormTm⁻¹-injective-in-PS : (∃[ mx ] (Cf ≡ X mx)) → (x' : Cf ► # 0) → (eqx : x' ≡ x)
                                        → (∃[ my ] (Cg ≡ X my)) → (y' : Cg ► # 0) → (eqy : y' ≡ y)
                                        → (k' : (Bf , Cf) ∈ (WkCon Γ ▹ (WkTy B , X (# 0)))) → (eqk : k' ≡ k)
                                        → (l' : (Bg , Cg) ∈ (WkCon Γ ▹ (WkTy B , X (# 0)))) → (eql : l' ≡ l)
                                        → (f'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bf))
                                        → (g'' : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , Bg))
                                        → (eqf' : f'' ≡ f')
                                        → (eqg' : g'' ≡ g')
                                        → 𝟙 ≡ B → f ≡ g
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl (.(# 0) , refl) (►-here refl) refl (∈-here refl) refl (∈-here refl) refl norm-term norm-term refl refl refl = refl
    lem-lem-extNormTm⁻¹-injective-in-PS (.(# 0) , refl) (►-here refl) refl _ _ _ (∈-drop k') _ _ refl _ _ _ refl = contradiction k' no-0-in-WkCon
    lem-lem-extNormTm⁻¹-injective-in-PS _ _ _ (.(# 0) , refl) (►-here refl) refl _ _ (∈-drop l') refl _ _ _ refl = contradiction l' no-0-in-WkCon

--------------------------------------------------------------------------------
-- Main lemma
--------------------------------------------------------------------------------

lem-PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (f g : NormTm Γ A) → f ≡ g

-- -- ps-term
lem-PSEq (ps-term _) norm-term norm-term = refl

-- ps-proj
lem-PSEq (ps-proj k pred x) (norm-proj y) (norm-proj z) = cong norm-proj (linTyProj pred y z)

-- ps-ext
lem-PSEq (ps-ext ps) f g = extNormTm⁻¹-injective-in-PS (ps-ext ps) f g (lem-PSEq ps (extNormTm⁻¹ f) (extNormTm⁻¹ g))

-- ps-const
lem-PSEq (ps-const ps) (norm-proj x) (norm-proj y) = cong norm-proj (linTyProj (ps-src-are-linear (ps-const ps)) x y)
lem-PSEq (ps-const ps) (norm-proj x) (norm-comp _ _ _) = contradiction x no-0-in-WkTy
lem-PSEq (ps-const ps) (norm-comp _ _ _) (norm-proj y) = contradiction y no-0-in-WkTy
lem-PSEq (ps-const ps) (norm-comp norm-term (∈-here refl) (►-here refl)) (norm-comp norm-term (∈-here refl) (►-here refl)) = refl
lem-PSEq (ps-const ps) _ (norm-comp g (∈-drop l) y) = contradiction (l , y) no-0-producer-in-WkCon
lem-PSEq (ps-const ps) (norm-comp f (∈-drop k) x) _ = contradiction (k , x) no-0-producer-in-WkCon
lem-PSEq (ps-const ps) (norm-comp (norm-proj x) (∈-here ()) x₂) (norm-comp g (∈-here x₃) x₄)
lem-PSEq (ps-const ps) (norm-comp (norm-comp f x x₁) (∈-here ()) x₃) (norm-comp g (∈-here x₄) x₅)
lem-PSEq (ps-const ps) (norm-comp (norm-pair f f₁) (∈-here ()) x₁) (norm-comp g (∈-here x₂) x₃)

-- ps-pair
lem-PSEq (ps-pair ps₁ ps₂) (norm-pair f f') (norm-pair g g') = cong₂ norm-pair (lem-PSEq ps₁ f g) (lem-PSEq ps₂ f' g')

-- ps-weak
lem-PSEq (ps-weak ps) f g = {!!} -- WkNormTm⁻¹-injective-in-PS (ps-weak ps) f g (lem-PSEq ps (WkNormTm⁻¹ f) (WkNormTm⁻¹ g))

--------------------------------------------------------------------------------
-- Main theoreme

PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (f g : Tm Γ A) → f ∼ g
PSEq ps f g = ≡NormTm→∼Tm f g (lem-PSEq ps (normalize f) (normalize g))
