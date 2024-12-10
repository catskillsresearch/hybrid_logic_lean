import Hybrid.ProofUtils

theorem MCS_pf (h : MCS Γ) : Γ ⊢ φ → φ ∈ Γ := by
  intro pf
  rw [←(@not_not (φ ∈ Γ))]
  intro habs
  have ⟨cons, pf_bot⟩ := h
  have ⟨pf_bot, _⟩ := not_forall.mp (pf_bot habs)
  clear h
  apply cons
  apply Γ_mp
  apply Deduction.mpr
  assumption
  assumption

theorem MCS_thm (h : MCS Γ) : ⊢ φ → φ ∈ Γ := by
  intro
  apply MCS_pf h
  apply Γ_theorem
  assumption

theorem MCS_mp (h : MCS Γ) (h1 : φ ⟶ ψ ∈ Γ) (h2 : φ ∈ Γ) : ψ ∈ Γ := by
  rw [←@not_not (ψ ∈ Γ)]
  intro habs
  have ⟨pf_bot, _⟩ := not_forall.mp (h.right habs)
  apply h.left
  apply Γ_mp
  apply Deduction.mpr
  assumption
  apply Γ_mp
  repeat (apply Γ_premise; assumption)

theorem MCS_conj {Γ : Set (Form N)} (hmcs : MCS Γ) (φ ψ : Form N) : (φ ∈ Γ ∧ ψ ∈ Γ) ↔ (φ ⋀ ψ) ∈ Γ := by
  apply Iff.intro
  . intro ⟨l, r⟩
    apply MCS_pf hmcs
    exact Γ_conj_intro (Γ_premise l) (Γ_premise r)
  . intro h
    apply And.intro <;> apply MCS_pf hmcs
    exact Γ_conj_elim_l (Γ_premise h)
    exact Γ_conj_elim_r (Γ_premise h)

theorem MCS_max {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∉ Γ ↔ (∼φ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    have ⟨pf_bot, _⟩ := not_forall.mp (hmcs.2 h)
    apply MCS_pf hmcs; apply Deduction.mpr
    exact pf_bot
  . intro h habs
    apply hmcs.1
    apply Γ_mp (Γ_premise h) (Γ_premise habs)

theorem MCS_impl {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∈ Γ → ψ ∈ Γ) ↔ ((φ⟶ψ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    by_cases hc : φ ∈ Γ
    . apply MCS_pf hmcs
      apply Deduction.mpr
      apply increasing_consequence
      exact Γ_premise (h hc)
      simp
    . simp only [MCS_max, hmcs, Form.neg] at hc
      apply MCS_pf hmcs; apply Deduction.mpr
      apply Γ_mp
      apply @Γ_theorem N (⊥ ⟶ ψ)
      apply tautology
      eval
      exact Deduction.mp (Γ_premise hc)
  . intro h1 h2
    apply MCS_pf hmcs
    exact Γ_mp (Γ_premise h1) (Γ_premise h2)

theorem MCS_iff {Γ : Set (Form N)} (hmcs : MCS Γ) : ((φ⟷ψ) ∈ Γ) ↔ (φ ∈ Γ ↔ ψ ∈ Γ) := by
  simp only [Form.iff, ←MCS_conj, ←MCS_impl, hmcs]
  apply Iff.intro
  <;> intros; apply Iff.intro
  . apply And.left
    assumption
  . apply And.right
    assumption
  apply And.intro <;> simp [*]

theorem MCS_rw {Γ : Set (Form N)} (hmcs : MCS Γ) (pf : ⊢ (φ ⟷ ψ)) : φ ∈ Γ ↔ ψ ∈ Γ := by
  rw [←MCS_iff hmcs]
  apply MCS_pf hmcs
  exact Γ_theorem pf Γ

lemma MCS_rich : ∀ {Θ : Set (Form N)}, (MCS Θ) → (witnessed Θ) → ∃ i : NOM N, ↑i ∈ Θ := by
  intro Θ mcs wit
  have := Proof.MCS_thm mcs (Proof.ax_name ⟨0⟩)
  have := wit this
  simp [subst_nom] at this
  exact this

lemma MCS_with_svar_witness : ∀ {Θ : Set (Form N)} {x y : SVAR} (_ : is_substable φ y x), (MCS Θ) → φ[y//x] ∈ Θ → (ex x, φ) ∈ Θ := by
  intro Θ x y h1 mcs h2
  apply MCS_mp mcs
  apply MCS_thm mcs
  apply ax_q2_svar_contrap h1
  repeat assumption
