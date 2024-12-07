import Hybrid.Form
import Hybrid.Util

structure Eval (N : Set ℕ) where
  f  : Form N → Bool
  p1 : f ⊥ = false
  p2 : ∀ φ ψ : Form N, (f (φ ⟶ ψ) = true) ↔ (¬(f φ) = true ∨ (f ψ) = true)

theorem e_dn {e : Eval N} : e.f (∼φ) = false ↔ e.f φ = true := by
  simp only [Form.neg, ←Bool.not_eq_true, e.p1, e.p2, not_or, not_not, and_true];
  sorry

theorem e_neg {e : Eval N} : e.f (∼φ) = true ↔ e.f φ = false := by
  have c := @not_congr (e.f (∼φ) = false) (e.f φ = true) e_dn
  rw [Bool.not_eq_false, Bool.not_eq_true] at c
  exact c

theorem e_conj {e : Eval N} : e.f (φ ⋀ ψ) = true ↔ (e.f φ = true ∧ e.f ψ = true) := by
  rw [Form.conj, ←Bool.not_eq_false, e_dn, e.p2, not_or, not_not, Bool.not_eq_true, e_dn]

theorem e_disj {e : Eval N} : e.f (φ ⋁ ψ) = true ↔ (e.f φ = true ∨ e.f ψ = true) := by
  rw [Form.disj, e.p2, Bool.not_eq_true, e_dn]

theorem e_impl {e : Eval N} : e.f (φ ⟶ ψ) = true ↔ (e.f φ = true → e.f ψ = true) := by
  simp only [e.p2, implication_disjunction]

syntax "eval" : tactic
macro_rules
  | `(tactic| eval) => `(tactic| intro e; simp [e.p1, e.p2, e_dn, e_neg, e_conj, e_disj, e_impl, -Form.neg, -Form.conj, -Form.disj, -Form.iff])
