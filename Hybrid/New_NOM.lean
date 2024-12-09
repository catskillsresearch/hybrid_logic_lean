import Hybrid.Form
import Hybrid.Util

def nom_occurs : NOM N → Form N → Bool
| i, .nom j    => i = j
| i, .impl ψ χ => (nom_occurs i ψ) || (nom_occurs i χ)
| i, .box ψ    => nom_occurs i ψ
| i, .bind _ ψ => nom_occurs i ψ
| _, _         => false

lemma new_nom_gt      : nom_occurs i φ → i.letter < φ.new_nom.letter   := by
  induction φ with
  | nom i          =>
      simp [nom_occurs, Form.new_nom, -implication_disjunction]
      intro h
      rw [h]
      exact Nat.lt_succ_self i.letter
  | impl ψ χ ih1 ih2 =>
      simp only [nom_occurs, Form.new_nom, Bool.or_eq_true, max]
      intro h
      apply Or.elim h
      . intro ha
        clear ih2 h
        have ih1 := ih1 ha
        by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
        . simp [hc]
          assumption
        . simp [hc]
          simp at hc
          exact Nat.lt_of_lt_of_le ih1 hc
      . intro hb
        clear ih1 h
        have ih2 := ih2 hb
        by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih2 hc
        . simp [hc]
          assumption
  | box      =>
      assumption
  | bind     =>
      assumption
  | _ => simp [nom_occurs]

lemma new_nom_is_nom  : nom_occurs (φ.new_nom) φ = false := by
  rw [←Bool.eq_false_eq_not_eq_true]
  intro h
  have a := new_nom_gt h
  have b := Nat.lt_irrefl φ.new_nom.letter
  exact b a

lemma ge_new_nom_is_new (h : x ≥ φ.new_nom) : nom_occurs x φ = false := by
  rw [←Bool.eq_false_eq_not_eq_true]
  intro habs
  have := new_nom_gt habs
  have a := Nat.lt_of_le_of_lt h this
  have b := Nat.lt_irrefl φ.new_nom.letter
  exact b a
