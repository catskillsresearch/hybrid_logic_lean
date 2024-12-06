import Mathlib
import Hybrid.Util
import Hybrid.Basics
import Hybrid.Substitution
import Hybrid.NominalSubstitution
open Substitution
open NominalSubstitution

section IteratedModalities

  -- Axiom utils. Since we won't be assuming a transitive frame,
  -- it will make sense to be able to construct formulas with
  -- iterated modal operators at their beginning (ex., for axiom nom)
  def iterate_nec (n : Nat) (φ : Form N) : Form N :=
    let rec loop : Nat → Form  N → Form N
      | 0, φ   => φ
      | n+1, φ => □ (loop n φ)
    loop n φ

  theorem iter_nec_one : □ φ = iterate_nec 1 φ := by
    rw [iterate_nec, iterate_nec.loop, iterate_nec.loop]

  theorem iter_nec_one_m_comm : iterate_nec 1 (iterate_nec m φ) = iterate_nec m (iterate_nec 1 φ) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop]
        exact ih

  theorem iter_nec_compose : iterate_nec (m + 1) φ = iterate_nec m (iterate_nec 1 φ) := by
    rw [iterate_nec, iterate_nec.loop, iter_nec_one, ←iterate_nec, iter_nec_one_m_comm]

  theorem iter_nec_succ : iterate_nec (m + 1) φ = iterate_nec m (□ φ) := by
    rw [iter_nec_one, iter_nec_compose]



  def iterate_pos (n : Nat) (φ : Form N) : Form N :=
    let rec loop : Nat → Form N → Form N
      | 0, φ   => φ
      | n+1, φ => ◇ (loop n φ)
    loop n φ

  theorem iter_pos_one : ◇ φ = iterate_pos 1 φ := by
    rw [iterate_pos, iterate_pos.loop, iterate_pos.loop]

  theorem iter_pos_one_m_comm : iterate_pos 1 (iterate_pos m φ) = iterate_pos m (iterate_pos 1 φ) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop]
        exact ih

  theorem iter_pos_compose : iterate_pos (m + 1) φ = iterate_pos m (iterate_pos 1 φ) := by
    rw [iterate_pos, iterate_pos.loop, iter_pos_one, ←iterate_pos, iter_pos_one_m_comm]

  theorem iter_pos_succ : iterate_pos (m + 1) φ = iterate_pos m (◇ φ) := by
    rw [iter_pos_one, iter_pos_compose]


end IteratedModalities

  theorem ex_depth {x : SVAR} : Form.depth φ < Form.depth (ex x, φ) := by
    simp [Form.depth]
    rw [←Nat.add_assoc, ←Nat.add_assoc, Nat.add_comm]
    apply Nat.lt_add_of_pos_right
    simp
