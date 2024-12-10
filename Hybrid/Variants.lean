import Hybrid.Model

@[simp]
theorem is_variant_refl {g : I W} (x : SVAR) : is_variant g g x := by simp

@[simp]
theorem is_variant_symm {g₁ : I W} {g₂ : I W} {x : SVAR} : is_variant g₁ g₂ x ↔ is_variant g₂ g₁ x := by
  -- bit annoying that it simplified the implication
  -- maybe prove again using simp [-implication_disjunction]
  simp
  apply Iff.intro
  . intro h1 hy
    apply Or.elim (h1 hy)
    . intro x_eq_y
      exact Or.inl x_eq_y
    . intro g1_eq_g2
      exact Or.inr (Eq.symm g1_eq_g2)
  . intro h2 hy
    apply Or.elim (h2 hy)
    . intro x_eq_y
      exact Or.inl x_eq_y
    . intro g2_eq_g1
      exact Or.inr (Eq.symm g2_eq_g1)

theorem is_variant_trans {g₁ g₂ g₃ : I W} {x : SVAR} : is_variant g₁ g₂ x → is_variant g₂ g₃ x → is_variant g₁ g₃ x := by
  rw [is_variant, is_variant, is_variant]
  intros a b y x_not_y
  have g1_is_g2 := a y x_not_y
  have g2_is_g3 := b y x_not_y
  exact Eq.trans g1_is_g2 g2_is_g3

theorem two_step_variant {g₁ g₂ g₃ : I W} {x y : SVAR} (g₁₂x : is_variant g₁ g₂ x) (g₂₃y : is_variant g₂ g₃ y) : ∀ v : SVAR, (v ≠ x ∧ v ≠ y) → g₁ v = g₃ v := by
  intro v ⟨v_not_x, v_not_y⟩
  have one_eq_two   := g₁₂x v (Ne.symm v_not_x)
  have two_eq_three := g₂₃y v (Ne.symm v_not_y)
  exact Eq.trans one_eq_two two_eq_three

theorem two_step_variant_rev (g₁ g₃ : I W) {x y : SVAR} (two_step : ∀ v : SVAR, (v ≠ x ∧ v ≠ y) → g₁ v = g₃ v) : ∃ g₂ : I W, (is_variant g₁ g₂ x ∧ is_variant g₂ g₃ y) := by
  let g₂ : I W := (λ v : SVAR => if (v = x) then (g₃ v) else if (v = y) then (g₁ v) else (g₃ v))
  exists g₂
  apply And.intro
  . rw [is_variant]
    intro v v_x
    have v_x := Ne.symm v_x
    sorry
  sorry

theorem variant_mirror_property (g₁ g₂ g₃ : I W) {x y : SVAR} (g₁₂x : is_variant g₁ g₂ x) (g₂₃y : is_variant g₂ g₃ y) :
  ∃ g₂_mirror : I W, (is_variant g₁ g₂_mirror y ∧ is_variant g₂_mirror g₃ x) := by
  have two_step := two_step_variant g₁₂x g₂₃y
  conv at two_step =>
    intro v
    conv => lhs ; rw [conj_comm]
  exact two_step_variant_rev g₁ g₃ two_step
