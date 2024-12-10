import Hybrid.GeneralModel

def Canonical : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := restrict_by MCS (λ Γ => λ Δ => (∀ {φ : Form TotalSet}, □φ ∈ Γ → φ ∈ Δ))
--  R := λ Γ => λ Δ => Γ.MCS ∧ Δ.MCS ∧ (∀ φ : Form, □φ ∈ Γ → φ ∈ Δ)
  Vₚ:= λ p => {Γ | MCS Γ ∧ ↑p ∈ Γ}
  Vₙ:= λ i => {Γ | MCS Γ ∧ ↑i ∈ Γ}

def CanonicalI : SVAR → Set (Set (Form TotalSet)) := λ x => {Γ | MCS Γ ∧ ↑x ∈ Γ}

instance : Membership (Form TotalSet) Canonical.W := ⟨Set.Mem⟩

theorem R_nec : □φ ∈ Γ → Canonical.R Γ Δ → φ ∈ Δ := by
  intro h1 h2
  simp only [Canonical, restrict_by] at h2
  apply h2.right.right
  assumption

theorem R_pos : Canonical.R Γ Δ ↔ (MCS Γ ∧ MCS Δ ∧ ∀ {φ}, (φ ∈ Δ → ◇φ ∈ Γ)) := by
  simp only [Canonical, restrict_by]
  apply Iff.intro
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    rw [←(@not_not (◇φ ∈ Γ))]
    intro habs
    have ⟨habs, _⟩ := not_forall.mp (h1.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg, Form.diamond] at habs
    have habs : ∼φ ∈ Δ := by
      apply h3
      apply Proof.MCS_pf h1
      apply Proof.Γ_mp
      apply Proof.Γ_theorem
      apply Proof.tautology
      apply dne
      assumption
    unfold MCS consistent at h1 h2
    apply h2.left
    apply Proof.Γ_mp
    repeat (apply Proof.Γ_premise; assumption)
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    rw [←(@not_not (φ ∈ Δ))]
    intro habs
    have ⟨habs, _⟩ := not_forall.mp (h2.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg] at habs
    have habs : ◇∼φ ∈ Γ := by
      apply h3
      apply Proof.MCS_pf h2
      assumption
    unfold MCS consistent at h1 h2
    apply h1.left
    apply Proof.Γ_mp
    apply Proof.Γ_premise
    assumption
    apply Proof.Γ_mp
    apply Proof.Γ_theorem
    apply Proof.mp
    apply Proof.tautology
    apply iff_elim_l
    apply Proof.dn_nec
    apply Proof.Γ_premise
    assumption

theorem R_iter_nec (n : ℕ) : (iterate_nec n φ) ∈ Γ → path Canonical.R Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  induction n generalizing φ Δ with
  | zero =>
      simp only [iterate_nec, iterate_nec.loop, path] at h1 h2
      rw [←h2]
      assumption
  | succ n ih =>
      simp only [path, iter_nec_succ] at ih h1 h2
      have ⟨Κ, hk1, hk2⟩ := h2
      apply R_nec
      exact (ih h1 hk2)
      assumption

theorem R_iter_pos (n : ℕ) : path Canonical.R Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  induction n generalizing φ Δ with
  | zero =>
      simp [path, iterate_pos, iterate_pos.loop] at h1 ⊢
      rw [h1]
      assumption
  | succ n ih =>
      simp only [path, iter_pos_succ] at ih h1 ⊢
      have ⟨Κ, hk1, hk2⟩ := h1
      rw [R_pos] at hk1
      apply ih hk2
      exact hk1.right.right h2

theorem restrict_R_iter_nec {n : ℕ} : (iterate_nec n φ) ∈ Γ → path (restrict_by R Canonical.R) Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  apply R_iter_nec
  assumption
  apply path_restr
  assumption

theorem restrict_R_iter_pos {n : ℕ} : path (restrict_by R Canonical.R) Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  apply R_iter_pos
  apply path_restr
  repeat assumption
