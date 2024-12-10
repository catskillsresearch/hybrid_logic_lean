import Hybrid.Canonical

-- implicitly we mean generated submodels *of the canonical model*
def Set.GeneratedSubmodel (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ =>
    (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧
    (∃ m, path (restrict_by restriction Canonical.R) Θ Δ m) ∧
    Canonical.R Γ Δ
  Vₚ:= λ p => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₚ p}
  Vₙ:= λ i => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₙ i}

def Set.GeneratedSubI (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralI (Set (Form TotalSet)) := λ x =>
  {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ CanonicalI x}

theorem submodel_canonical_path (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) (rt : r Θ) : path (Θ.GeneratedSubmodel r).R Γ Δ n → path (restrict_by r Canonical.R) Γ Δ n := by
  intro h
  induction n generalizing Γ Δ with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n ih =>
      have ⟨Η, ⟨h1, h2⟩⟩ := h
      have := ih h2
      clear h h2
      exists Η
      apply And.intro
      . simp [Set.GeneratedSubmodel] at h1
        have ⟨⟨n, l1⟩, ⟨⟨m, l2⟩, l3⟩⟩ := h1
        simp [restrict_by, l3]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption
      . exact this

theorem path_root (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) : path (restrict_by r Canonical.R) Θ Γ n → path (Θ.GeneratedSubmodel r).R Θ Γ n := by
  induction n generalizing Θ Γ with
  | zero => simp [path]
  | succ n ih =>
      simp only [path]
      intro ⟨Δ, ⟨h1, h2⟩⟩
      exists Δ
      apply And.intro
      . simp [Set.GeneratedSubmodel]
        apply And.intro
        . exists n
        . apply And.intro
          . exists (n+1)
            simp [path]
            exists Δ
          . exact h1.2.2
      . apply ih
        exact h2
