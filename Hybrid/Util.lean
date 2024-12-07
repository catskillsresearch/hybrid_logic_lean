import Mathlib
import Hybrid.TypeIff
open Classical

noncomputable def choice_intro (q : α → Sort u) (p : α → Prop) (P : ∃ a, p a) : (∀ a, p a → q a) → q P.choose := by
  intro h
  exact (h P.choose P.choose_spec)

theorem eq_symm : (a = b) ↔ (b = a) := eq_comm

@[simp]
theorem double_negation : ¬¬p ↔ p := Decidable.not_not

@[simp]
theorem implication_disjunction : (p → q) ↔ (¬p ∨ q) := Decidable.imp_iff_not_or

@[simp]
theorem negated_disjunction : ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or

@[simp]
theorem negated_conjunction : ¬(p ∧ q) ↔ ¬p ∨ ¬q := Decidable.not_and_iff_or_not

@[simp]
theorem negated_impl : ¬(p → q) ↔ p ∧ ¬q := Decidable.not_imp_iff_and_not

universe u
@[simp]
theorem negated_universal {α : Type u} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := not_forall

@[simp]
theorem negated_existential {α : Type u} {p : α → Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := not_exists

@[simp]
theorem conj_comm : p ∧ q ↔ q ∧ p := And.comm

theorem disj_comm : p ∨ q ↔ q ∨ p := Or.comm

theorem contraposition (p q : Prop) : (p → q) ↔ (¬q → ¬p) := Iff.symm Decidable.not_imp_not
