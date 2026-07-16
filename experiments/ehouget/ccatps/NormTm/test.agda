
  WkNormTm⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {m : Fin n} (f : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc m))) → NormTm Γ (A , X m)
  WkNormTm⁻¹ (norm-proj x) = norm-proj (Wk►⁻¹ x)
  WkNormTm⁻¹ (norm-comp f (∈-here refl) (►-here ()))
  WkNormTm⁻¹ {n} {Γ ▹ (src , tgt)} {A} {C} {k} (norm-comp {B = .(WkTy src)} {C = .(WkTy tgt)} f (∈-drop (∈-here refl)) x) = norm-comp (WkNormTm⁻¹-aux f) (∈-here refl) (Wk►⁻¹ x)
  WkNormTm⁻¹ {n} {Γ ▹ (src , tgt)} {A} {C} {k} (norm-comp {B = B} {C = C₁} f (∈-drop (∈-drop l)) x) = norm-comp {!!} (∈-drop {!!}) {!!}
    -- where
    -- WkNormTm⁻¹-lem : (f' : NormTm (WkCon Γ ▹ (WkTy C , X (# 0))) (WkTy A , B))
    --                → (eqf : f' ≡ f)
    --                → ∃[ A' ] ((B , C₁) ≡ WkArr A')
    --                → NormTm Γ (A , X k)
    -- WkNormTm⁻¹-lem f' eqf ((X m , C'') , refl) = norm-comp (WkNormTm⁻¹ f) (Wk∈⁻¹ l) (Wk►⁻¹ x)
    -- WkNormTm⁻¹-lem f' eqf ((𝟙 , C'') , refl) = norm-comp norm-term (Wk∈⁻¹ l) (Wk►⁻¹ x)
    -- WkNormTm⁻¹-lem (norm-pair f' f'') eqf ((B'' × B''' , C'') , refl) = norm-comp (norm-pair (WkNormTm⁻¹-aux f') (WkNormTm⁻¹-aux f'')) (Wk∈⁻¹ l) (Wk►⁻¹ x)
