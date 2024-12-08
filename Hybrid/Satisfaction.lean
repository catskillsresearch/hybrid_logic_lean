import Hybrid.Model

set_option linter.docPrime false

theorem bind_comm {M : Model N} {s : M.W} {g : I M.W} {φ : Form N} {x y : SVAR} : ((M,s,g) ⊨ all x, (all y, φ)) ↔ ((M,s,g) ⊨ all y, (all x, φ)) := by
  apply Iff.intro
  . intro h1
    intros h var_h_g i var_i_h
    have two_step : ∀ (v : SVAR), v ≠ x ∧ v ≠ y → g v = i v := (λ a => λ b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
    have exist_mid_g := two_step_variant_rev g i two_step
    match exist_mid_g with
    | ⟨mid_g, mid_g_var_g, mid_g_var_i⟩ =>
      have mid_g_sat := h1 mid_g (is_variant_symm.mp mid_g_var_g)
      exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)
  . intro h2
    intros h var_h_g i var_i_h
    have two_step : ∀ (v : SVAR), v ≠ y ∧ v ≠ x → g v = i v := (λ a => λ b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
    have exist_mid_g := two_step_variant_rev g i two_step
    match exist_mid_g with
    | ⟨mid_g, mid_g_var_g, mid_g_var_i⟩ =>
      have mid_g_sat := h2 mid_g (is_variant_symm.mp mid_g_var_g)
      exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)

theorem SatConjunction (Γ : Set (Form N)) (L : List Γ) : Γ ⊨ conjunction Γ L := by
  intro M s g M_sat_Γ
  induction L with
  | nil =>
      simp only [conjunction, Sat]
  | cons h t ih =>
      simp only [conjunction, and_sat, ih, and_true]
      exact M_sat_Γ h h.prop

theorem SetEntailment (Γ : Set (Form N)) : (∃ L, ⊨ (conjunction Γ L ⟶ ψ)) → Γ ⊨ ψ := by
  intro h
  intro M s g M_sat_Γ
  match h with
  | ⟨L, hw⟩ =>
      have l1 := hw M s g
      have l2 := SatConjunction Γ L M s g M_sat_Γ
      rw [Sat] at l1
      exact l1 l2
