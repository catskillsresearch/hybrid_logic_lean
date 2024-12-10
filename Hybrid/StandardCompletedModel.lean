import Hybrid.CompletedModel

-- pg. 638: "we only glue on a dummy state when we are forced to"
--    we define the set of states as Γ.MCS_in ∨ Γ.is_dummy
--    where is_dummy contains the assumption that we are *forced*
--    to glue a dummy
noncomputable def StandardCompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Model TotalSet :=
    ⟨{Γ : Set (Form TotalSet) // Γ.MCS_in mcs wit ∨ Γ.is_dummy mcs wit},
      λ Γ => λ Δ => (CompletedModel mcs wit).R Γ.1 Δ.1,
      λ p => {Γ | Γ.1 ∈ ((CompletedModel mcs wit).Vₚ p)},
      λ i => ⟨(completed_singleton_valuation mcs wit i).choose, choose_subtype mcs wit⟩⟩

noncomputable def StandardCompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : I (StandardCompletedModel mcs wit).W :=
    λ x => ⟨(completed_singleton_i mcs wit x).choose, choose_subtype' mcs wit⟩

theorem sat_dual_all_ex : ((M,s,g) ⊨ (all x, φ)) ↔ (M,s,g) ⊨ ∼(ex x, ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    simp only [Form.bind_dual, neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    have := h g' var
    simp only [Form.bind_dual, neg_sat, not_not] at this
    exact this

theorem sat_dual_nec_pos : ((M,s,g) ⊨ (□ φ)) ↔ (M,s,g) ⊨ ∼(◇ ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro _ _
    simp only [neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro s' r
    have := h s' r
    simp only [neg_sat, not_not] at this
    exact this

@[simp]
def coe (Δ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (h : Δ.MCS_in mcs wit) : (StandardCompletedModel mcs wit).W := ⟨Δ, Or.inl h⟩

def statement (φ : Form TotalSet) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := ∀ {Δ : Set (Form TotalSet)}, (h : Δ.MCS_in mcs wit) → φ ∈ Δ ↔ (StandardCompletedModel mcs wit, coe Δ mcs wit h, StandardCompletedI mcs wit) ⊨ φ


lemma truth_bttm : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement ⊥ mcs wit) := by
  intro _ mcs' wit' Δ h
  have := (mcs_in_prop mcs' wit' h).1
  apply Iff.intro
  . intro h
    exact this.1 (Proof.Γ_premise h)
  . simp

lemma truth_prop : ∀ {Θ : Set (Form TotalSet)} {p : PROP}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement p mcs wit) := by
  intro Θ  _ mcs wit Δ h
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h)
  apply Iff.intro
  . intro hl
    apply And.intro
    . apply mcs_in_wit
      exact h
    . simp [Canonical, hl, D_mcs]
  . simp [StandardCompletedModel, CompletedModel, WitnessedModel, Set.GeneratedSubmodel, restrict_by, Canonical, -implication_disjunction]
    intros
    assumption

lemma truth_nom_help : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ ((StandardCompletedModel mcs wit).Vₙ ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedModel, CompletedModel, WitnessedModel]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by
      simp [Set.GeneratedSubmodel, WitnessedModel] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . simp [Canonical, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [←@not_not (((Θ.GeneratedSubmodel witnessed).Vₙ i) = ∅), ←Ne,
          ←Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Δ
        exact delta_mem
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by simp [eta_eq]
      apply subsingleton_valuation i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Γ_premise
        exact a.left.left
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by simp [eta_eq]
      simp [Set.GeneratedSubmodel, Canonical] at eta_mem
      exact eta_mem.left.right

lemma truth_svar_help : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ (StandardCompletedI mcs wit ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedI, CompletedI, WitnessedI]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ Θ.GeneratedSubI witnessed i := by
      simp [Set.GeneratedSubI, WitnessedI] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . simp [CanonicalI, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [←@not_not ((Θ.GeneratedSubI witnessed i) = ∅), ←Ne,
          ←Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Δ
        exact delta_mem
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      apply subsingleton_i i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Γ_premise
        exact a.left.left
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      simp [Set.GeneratedSubI, CanonicalI] at eta_mem
      exact eta_mem.right.right

lemma truth_nom : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_nom_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_nom_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_svar : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_svar_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_svar_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_impl : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement φ mcs wit) → (statement ψ mcs wit) → statement (φ ⟶ ψ) mcs wit := by
  intro Θ mcs wit ih_φ ih_ψ Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  . intro h1 h2
    apply (ih_ψ h_in).mp
    apply Proof.MCS_mp
    repeat assumption
    exact (ih_φ h_in).mpr h2
  . intro sat_φ_ψ
    unfold statement at ih_φ ih_ψ
    rw [Sat, ←ih_φ, ←ih_ψ, Proof.MCS_impl] at sat_φ_ψ
    repeat assumption

lemma has_state_symbol (s : (StandardCompletedModel mcs wit).W) : (∃ i, (StandardCompletedModel mcs wit).Vₙ i = s) ∨ (∃ x, StandardCompletedI mcs wit x = s) := by
  apply Or.elim s.2
  . intro s_in
    apply Or.inl
    have ⟨s_mcs, s_wit⟩ := (mcs_in_prop mcs wit s_in)
    have ⟨i, sat_i⟩ := Proof.MCS_rich s_mcs s_wit
    simp [truth_nom mcs wit s_in] at sat_i
    exists i
    apply Eq.symm
    exact sat_i
  -- absolutely unnecesarily ugly, but at least it works
  . intro ⟨needs_dummy, s_is_dummy⟩
    have : s.1 = Set.singleton Form.bttm := by simp [s_is_dummy]; apply Eq.refl
    rw [needs_dummy, ←this] at needs_dummy
    clear this
    apply Or.elim needs_dummy
    . intro ⟨i, h⟩
      apply Or.inl
      exists i
      simp [StandardCompletedModel]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h,]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      exact eq
    . intro ⟨i, h⟩
      apply Or.inr
      exists i
      simp [StandardCompletedI]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      exact eq

def exists_replace : ⊢ ((ex x, φ.replace_bound y) ⟶ (ex x, φ)) := by
  sorry

lemma truth_ex : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (∀ {χ : Form TotalSet}, χ.depth < (ex x, ψ).depth → statement χ mcs wit) → statement (ex x, ψ) mcs wit := by
  intro Θ mcs wit ih
  intro Δ Δ_in
  have ⟨Δ_mcs, Δ_wit⟩ := (mcs_in_prop mcs wit Δ_in)
  apply Iff.intro
  . intro h
    have ⟨i, mem⟩ := Δ_wit h
    have ih_s := @ih (ψ[i//x]) subst_depth''
    rw [ih_s Δ_in] at mem
    apply WeakSoundness Proof.ax_q2_contrap
    exact mem
  . simp only [ex_sat]
    intro ⟨g', g'_var, g'_ψ⟩
    let s := g' x
    apply Or.elim (has_state_symbol s)
    . intro ⟨i, sat_i⟩
      have ih_s := @ih (ψ[i//x]) subst_depth''
      simp at sat_i
      rw [←nom_substitution (is_variant_symm.mp g'_var) (Eq.symm sat_i), ←ih_s] at g'_ψ
      have g'_ψ := Proof.Γ_premise g'_ψ
      clear g'_var sat_i
      apply Proof.MCS_pf Δ_mcs
      apply Proof.Γ_mp
      . apply Proof.Γ_theorem
        apply Proof.ax_q2_contrap
        exact i
      . exact g'_ψ
    . intro ⟨y, sat_y⟩
      simp at sat_y
      have := rename_all_bound ψ y (StandardCompletedModel mcs wit) (coe Δ mcs wit Δ_in) g'
      rw [iff_sat] at this
      rw [this] at g'_ψ
      clear this
      rw [←svar_substitution (substable_after_replace ψ) (is_variant_symm.mp g'_var) (Eq.symm sat_y)] at g'_ψ
      have r_ih := @ih ((ψ.replace_bound y)[y//x]) replace_bound_depth'
      rw [←r_ih] at g'_ψ
      have := Proof.MCS_with_svar_witness (substable_after_replace ψ) Δ_mcs g'_ψ
      apply Proof.MCS_mp Δ_mcs; apply Proof.MCS_thm Δ_mcs
      apply exists_replace; exact y; exact this
