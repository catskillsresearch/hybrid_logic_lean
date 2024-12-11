import Hybrid.Soundness
import Hybrid.ProofUtils

theorem satisfiable_iff_nocontradiction (Γ : Set (Form N)) : satisfiable Γ ↔ Γ ⊭ ⊥ := by
  apply Iff.intro <;> {
  . intro h
    simp at h ⊢
    conv => rhs; intro M; rhs; intro s; rhs; intro g; intro φ; rw [disj_comm]
    exact h
  }

theorem unsatisfiable_iff_contradiction (Γ : Set (Form N)) : ¬satisfiable Γ ↔ Γ ⊨ ⊥ := by
  conv => rhs; rw [←@not_not (Γ ⊨ ⊥)]
  apply Iff.not
  apply satisfiable_iff_nocontradiction

theorem notsatnot {Γ : Set (Form N)} {φ : Form N} : (Γ⊨φ) ↔ ¬satisfiable (Γ ∪ {∼φ}) := by
  rw [unsatisfiable_iff_contradiction, ←SemanticDeduction, ←Form.neg, Entails, Entails]
  conv => rhs; intro M s g h; rw [neg_sat, neg_sat, not_not]

def dn_equiv_premise {φ : Form N} : Γ ⊢ (∼∼φ) iff Γ ⊢ φ := by
  have l1 := Proof.tautology (@dne N φ)
  have l2 := Proof.tautology (@dni N φ)
  rw [SyntacticConsequence, SyntacticConsequence]
  apply TypeIff.intro
  repeat (
    intro ⟨L, _⟩;
    exists L;
    apply hs;
    repeat assumption
  )

theorem notprove_consistentnot : (Γ ⊬ φ) → consistent (Γ ∪ {∼φ}) := by
  intro h
  rw [←@not_not (consistent (Γ ∪ {∼φ}))]
  intro habs
  sorry

def completeness_statement := λ (N : Set ℕ) => (∀ (Γ : Set (Form N)) (φ : Form N), Γ ⊨ φ → (∃ _ : Γ ⊢ φ, True))

def cons_sat_statement     := λ (N : Set ℕ) => (∀ (Γ : Set (Form N)), consistent Γ → satisfiable Γ)

theorem ModelExistence {N : Set ℕ} : completeness_statement N ↔ cons_sat_statement N := by
  apply Iff.intro
  . intro h
    rw [←@not_not (cons_sat_statement N)]
    intro habs
    rw [cons_sat_statement, negated_universal] at habs
    match habs with
    | ⟨Δ, hw⟩ =>
      rw [negated_impl] at hw
      have ⟨consistent, not_satisfiable⟩  := hw
      rw [unsatisfiable_iff_contradiction] at not_satisfiable
      have ⟨by_completeness, _⟩ := (h Δ ⊥) not_satisfiable
      exact consistent by_completeness
  . rw [contraposition (cons_sat_statement N) (completeness_statement N)]
    intro h
    simp only [completeness_statement, not_forall, negated_impl, notsatnot, ←conj_comm] at h
    simp only [cons_sat_statement, not_forall, negated_impl]
    have ⟨Γ, φ, wit_l, wit_r⟩ := h
    exists (Γ ∪ {∼φ})
    sorry

noncomputable def Completeness : (∀ (Γ : Set (Form N)) (φ : Form N), Γ ⊨ φ → Γ ⊢ φ) := by
  intros h1 h2 h3; apply Exists.choose
  revert h1 h2 h3
  rw [←completeness_statement, ModelExistence]
  unfold cons_sat_statement
  sorry
