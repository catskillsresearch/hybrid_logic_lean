import Hybrid.WitnessedModel
import Hybrid.MCS

def CompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ => ((WitnessedModel mcs wit).R Γ Δ) ∨ (Γ = {Form.bttm} ∧ Δ = Θ)
  Vₚ:= λ p => (WitnessedModel mcs wit).Vₚ p
  Vₙ:= λ i => sorry

def CompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralI (Set (Form TotalSet)) := λ x =>
  sorry

-- Lemma 3.11, Blackburn 1998, pg. 637
lemma subsingleton_valuation : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (i : NOM TotalSet), MCS Θ → ((Θ.GeneratedSubmodel R).Vₙ i).Subsingleton := by
  -- the hypothesis MCS Θ is not necessary
  --  but to prove the theorem without it would complicate
  --  the code, and anyway, we'll only ever use MCS-generated submodels
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr i Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  sorry

lemma subsingleton_i : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (x : SVAR), MCS Θ → ((Θ.GeneratedSubI R) x).Subsingleton := by
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr x Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  rw [←(@not_not (Γ = Δ))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro ⟨φ, h⟩
  apply Or.elim h
  . clear h
    intro ⟨h3, h4⟩
    apply h4
    sorry
  . clear h
    intro ⟨h3, h4⟩
    apply h3
    sorry

lemma wit_subsingleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ((WitnessedModel mcs wit).Vₙ i).Subsingleton := by
  rw [WitnessedModel]
  apply subsingleton_valuation
  assumption

lemma wit_subsingleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ((WitnessedI mcs wit) x).Subsingleton := by
  rw [WitnessedI]
  apply subsingleton_i
  assumption

lemma completed_singleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ∃ Γ : Set (Form TotalSet), (CompletedModel mcs wit).Vₙ i = {Γ} := by
  sorry

lemma completed_singleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ∃ Γ : Set (Form TotalSet), (CompletedI mcs wit) x = {Γ} := by
  sorry

def Set.MCS_in (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Prop := ∃ n, path (WitnessedModel mcs wit).R Θ Γ n

theorem mcs_in_prop {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (MCS Γ ∧ witnessed Γ) := by
  intro ⟨n, h⟩
  cases n with
  | zero =>
      simp [path] at h
      simp [←h, mcs, wit]
  | succ n =>
      have ⟨Δ, h1, h2⟩ := h
      clear h2
      simp [WitnessedModel, Set.GeneratedSubmodel, Canonical] at h1
      have ⟨h3, ⟨m, h4⟩, h5⟩ := h1
      clear h1 h3
      simp [h5.2.1]
      apply path_restr' h4
      exact wit

theorem mcs_in_wit {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) := by
  intro ⟨n, h⟩
  exists n
  cases n with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n =>
      simp [path]
      have ⟨Δ, h1, h2⟩ := h
      exists Δ
      apply And.intro
      . apply submodel_canonical_path
        repeat assumption
      . have ⟨⟨_, l⟩, ⟨⟨_, r1⟩, r2⟩⟩ := h1
        simp [restrict_by, r2]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption

def needs_dummy {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := (∃ i, ((CompletedModel mcs wit).Vₙ i) = { (Set.singleton Form.bttm) }) ∨
                                                                                 (∃ x, ((CompletedI mcs wit) x) = { (Set.singleton Form.bttm) })

def Set.is_dummy (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := needs_dummy mcs wit ∧ Γ = {Form.bttm}

theorem choose_subtype {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)  : ((completed_singleton_valuation mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_valuation mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  . apply Or.inl
    sorry

theorem choose_subtype' {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : ((completed_singleton_i mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_i mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  sorry
