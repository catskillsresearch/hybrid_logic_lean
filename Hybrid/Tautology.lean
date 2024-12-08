import Hybrid.Eval

def Tautology (φ : Form N) : Prop := ∀ e : Eval N, e.f φ = true

theorem ax_1 : Tautology (φ ⟶ ψ ⟶ φ) := by
  intro e
  simp only [e.p2, Bool.not_eq_true, or_comm, ←or_assoc, Bool.dichotomy, true_or]

theorem neg_conj : Tautology ((φ ⟶ ∼ψ) ⟷ ∼(φ ⋀ ψ)) := by
  simp
  eval

theorem contrapositive : Tautology ((φ ⟶ ψ) ⟶ (∼ψ ⟶ ∼φ)) := by
  eval
  simp only [or_comm]
  simp only [and_or_right]
  apply And.intro
  . rw [←or_assoc, ←Bool.not_eq_true]
    apply Or.inl
    apply em
  . rw [←or_comm, or_assoc, or_comm, ←Bool.not_eq_true]
    apply Or.inl
    apply em

theorem contrapositive' : Tautology ((∼ψ ⟶ ∼φ) ⟶ (φ ⟶ ψ)) := by
  eval
  simp only [or_comm]
  simp only [and_or_right]
  apply And.intro
  . rw [←or_assoc, ←Bool.not_eq_true]
    apply Or.inl
    rw [or_comm]
    apply em
  . rw [←or_comm, or_assoc, or_comm, ←Bool.not_eq_true]
    apply Or.inl
    rw [or_comm]
    apply em

theorem neg_intro : Tautology ((φ ⟶ ψ) ⟶ (φ ⟶ ∼ψ) ⟶ ∼φ) := by
    eval
    sorry

theorem imp_refl : Tautology (φ ⟶ φ) := by
  eval

theorem imp_neg : Tautology (∼(φ ⟶ ψ) ⟷ (φ ⋀ ∼ψ)) := by
  simp only [Form.iff, Form.conj, Form.neg]
  eval

theorem dne : Tautology (∼∼φ ⟶ φ) := by
  eval

theorem dni : Tautology (φ ⟶ ∼∼φ) := by
  eval

theorem dn : Tautology (φ ⟷ ∼∼φ) := by
  intro e
  rw [Form.iff, e_conj]
  exact ⟨dni e, dne e⟩

theorem conj_intro : Tautology (φ ⟶ ψ ⟶ (φ ⋀ ψ)) := by
  eval
  sorry

theorem conj_intro_hs : Tautology ((φ ⟶ ψ) ⟶ (φ ⟶ χ) ⟶ (φ ⟶ (ψ ⋀ χ))) := by
  eval
  sorry

theorem conj_elim_l : Tautology ((φ ⋀ ψ) ⟶ φ) := by
  eval
  simp [←or_assoc, or_comm, Bool.dichotomy]

theorem conj_elim_r : Tautology ((φ ⋀ ψ) ⟶ ψ) := by
  eval
  simp [or_assoc, Bool.dichotomy]

theorem conj_comm_t : Tautology ((φ ⋀ ψ) ⟶ (ψ ⋀ φ)) := by
  eval
  sorry

theorem conj_comm_t' : Tautology (∼(φ ⋀ ψ) ⟶ ∼(ψ ⋀ φ)) := by
  simp only [Form.neg, Form.conj]
  eval
  sorry

theorem iff_intro : Tautology ((φ ⟶ ψ) ⟶ (ψ ⟶ φ) ⟶ (φ ⟷ ψ)) := by
  sorry

theorem iff_elim_l : Tautology ((φ ⟷ ψ) ⟶ (φ ⟶ ψ)) := by
  sorry

theorem iff_elim_r : Tautology ((φ ⟷ ψ) ⟶ (ψ ⟶ φ)) := by
  sorry

theorem iff_rw : Tautology ((φ ⟷ ψ) ⟶ (ψ ⟷ χ) ⟶ (φ ⟷ χ)) := by
  sorry

theorem iff_imp : Tautology ((φ ⟷ ψ) ⟶ (χ ⟷ τ) ⟶ ((φ ⟶ χ) ⟷ (ψ ⟶ τ))) := by
  sorry

theorem taut_iff_mp : Tautology (φ ⟷ ψ) → Tautology (φ ⟶ ψ) := by
  rw [Form.iff]
  intro h e
  have := h e
  rw [e_conj] at this
  exact this.left

theorem taut_iff_mpr : Tautology (φ ⟷ ψ) → Tautology (ψ ⟶ φ) := by
  rw [Form.iff]
  intro h e
  have := h e
  rw [e_conj] at this
  exact this.right

theorem disj_intro_l : Tautology (φ ⟶ (φ ⋁ ψ)) := by
  eval
  sorry

theorem disj_intro_r : Tautology (φ ⟶ (ψ ⋁ φ)) := by
  eval
  sorry

theorem disj_elim : Tautology ((φ ⋁ ψ) ⟶ (φ ⟶ χ) ⟶ (ψ ⟶ χ) ⟶ χ) := by
  eval
  sorry

theorem idem : Tautology ((χ ⟶ ψ ⟶ ψ ⟶ φ) ⟶ (χ ⟶ ψ ⟶ φ)) := by
  eval
  sorry

theorem exp : Tautology (((φ ⋀ ψ) ⟶ χ) ⟶ (φ ⟶ ψ ⟶ χ)) := by
  intro e
  sorry

theorem imp : Tautology ((φ ⟶ ψ ⟶ χ) ⟶ ((φ ⋀ ψ)) ⟶ χ) := by
  intro e
  sorry

theorem impexp : Tautology (((φ ⋀ ψ) ⟶ χ) ⟷ (φ ⟶ ψ ⟶ χ)) := by
  intro e
  rw [Form.iff, e_conj]
  exact ⟨exp e, imp e⟩

theorem com12 : Tautology ((φ ⟶ (ψ ⟶ χ)) ⟶ (ψ ⟶ (φ ⟶ χ))) := by
  intro e
  simp only [e_impl]
  intro h1 h2 h3
  exact h1 h3 h2

theorem mp_help : Tautology ((a ⟶ (φ ⟶ ψ)) ⟶ ((b ⟶ φ) ⟶ (a ⟶ b ⟶ ψ))) := by
  sorry

def Eval.nom_variant (e e' : Eval N) (i : NOM N) (x : SVAR) : Prop :=
  e'.f = (λ φ : Form N => if φ = i then (e.f x) else (e.f φ))

theorem iff_not : Tautology ((φ ⟷ ψ) ⟷ (∼φ ⟷ ∼ψ)) := by
  simp only [Form.iff, Form.conj, Form.neg]
  eval

theorem imp_taut (h : Tautology φ) : Tautology ((φ ⟶ ψ) ⟶ ψ) := by
  unfold Tautology at h ⊢
  intro e
  have := h e
  simp [this, e.p1, e.p2, e_dn, e_neg, e_conj, e_disj, e_impl, -Form.neg, -Form.conj, -Form.disj, -Form.iff]
