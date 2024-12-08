
import Hybrid.FormSubstitution


set_option trace.split.failure true

lemma svar_eq {ψ χ : SVAR} : ψ = χ ↔ ψ.1 = χ.1 := by
  have l1 : ψ = ⟨ψ.letter⟩ := by simp
  have l2 : χ = ⟨χ.letter⟩ := by simp
  rw [l1, l2]
  simp

lemma new_var_neg : (∼ψ).new_var = ψ.new_var := by
  simp [Form.new_var, max, -implication_disjunction]
  rw [←svar_eq]
  intro _
  simp [*]

lemma subst_neg : is_substable (∼ψ) y x ↔ is_substable ψ y x := by
  simp [is_substable]

lemma new_var_gt      : occurs x φ → x < φ.new_var   := by
  induction φ with
  | svar y          =>
      simp [occurs, Form.new_var, -implication_disjunction]
      intro h
      rw [h]
      exact Nat.lt_succ_self y.letter
  | impl ψ χ ih1 ih2 =>
      simp only [occurs, Form.new_var, Bool.or_eq_true, max]
      intro h
      apply Or.elim h
      . intro ha
        clear ih2 h
        have ih1 := ih1 ha
        by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
        . simp [hc]
          assumption
        . simp [hc]
          simp at hc
          exact Nat.lt_of_lt_of_le ih1 hc
      . intro hb
        clear ih1 h
        have ih2 := ih2 hb
        by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih2 hc
        . simp [hc]
          assumption
  | box ψ ih      =>
      simp only [occurs, Form.new_var]
      assumption
  | bind y ψ ih   =>
      simp only [occurs, Form.new_var, max]
      intro h
      have ih := ih h
      by_cases hc : (y + 1).letter > (Form.new_var ψ).letter
      . simp [hc]
        simp at hc
        exact Nat.lt_trans ih hc
      . simp [hc]
        assumption
  | _ => simp [occurs]

lemma new_var_is_new  : occurs (φ.new_var) φ = false := by
  rw [←Bool.eq_false_eq_not_eq_true]
  intro h
  have a := new_var_gt h
  have b := Nat.lt_irrefl φ.new_var.letter
  exact b a

lemma ge_new_var_is_new (h : x ≥ φ.new_var) : occurs x φ = false := by
  rw [←Bool.eq_false_eq_not_eq_true]
  intro habs
  have := new_var_gt habs
  have a := Nat.lt_of_le_of_lt h this
  have b := Nat.lt_irrefl φ.new_var.letter
  exact b a

lemma new_var_geq1 : x ≥ (φ ⟶ ψ).new_var → (x ≥ φ.new_var ∧ x ≥ ψ.new_var) := by
intro h
simp [Form.new_var, max] at *
split at h
. apply And.intro
  . assumption
  . apply Nat.le_trans _ h
    apply Nat.le_of_lt
    assumption
. apply And.intro
  . simp at *
    apply Nat.le_trans _ h
    assumption
  . assumption

lemma new_var_geq2 : x ≥ (all y, ψ).new_var → (x ≥ (y+1) ∧ x ≥ ψ.new_var) := by
intro h
simp [Form.new_var, max] at *
split at h
. apply And.intro
  . apply Nat.le_trans _ h
    apply Nat.le_of_lt
    assumption
  . assumption
. apply And.intro
  . assumption
  . simp at *
    apply Nat.le_trans _ h
    assumption

lemma new_var_geq3 : x ≥ (□ φ).new_var → (x ≥ φ.new_var) := by simp [Form.new_var]

lemma notfree_after_subst {φ : Form N} {x y : SVAR} (h : x ≠ y) : is_free x (φ[y // x]) = false := by
  induction φ with
  | svar z   =>
      by_cases xz : x = z
      . simp [subst_svar, if_pos xz, is_free, h]
      . simp [subst_svar, if_neg xz, is_free, xz]
  | impl _ _ ih1 ih2 =>
      simp [subst_svar, is_free, ih1, ih2]
  | box _ ih    =>
      simp [subst_svar, is_free, ih]
  | bind z _ ih =>
      by_cases xz : x = z
      . simp [subst_svar, xz, is_free]
      . simp [subst_svar, if_neg xz, is_free, ih]
  | _        => simp only [is_free]

lemma notoccursbind : occurs x φ = false → occurs x (all v, φ) = false := by
  simp [occurs]

lemma notoccurs_notfree : (occurs x φ = false) → (is_free x φ = false) := by
  induction φ with
  | svar _ => simp [occurs, is_free]
  | impl _ _ ih1 ih2 =>
      intro h
      simp [occurs] at h
      simp [is_free, ih1, ih2, h]
  | box _ ih        =>
      intro h
      rw [occurs] at h
      simp [is_free, ih, h]
  | bind _ _ ih     =>
      intro h
      rw [occurs] at h
      simp [is_free, ih, h]
  | _ =>
      intro h
      rfl

lemma preserve_notfree {φ : Form N} (x v : SVAR) : (is_free x φ = false) → (is_free x (all v, φ) = false) := by
  intro h
  simp only [is_free, h, Bool.and_false]

lemma subst_notfree_var {φ : Form N} {x y : SVAR} (h : is_free x φ = false) : (φ[y // x] = φ) ∧ (occurs x φ = false → is_substable φ y x) := by
  induction φ with
  | svar z =>
      by_cases heq : x = z
      . simp only [is_free, heq, beq_self_eq_true] at h
      . simp only [subst_svar, heq, ite_false, occurs, is_substable]
  | impl ψ χ ih1 ih2 =>
      simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h
      apply And.intro
      . simp [subst_svar, h, ih1, ih2]
      . intro nocc
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc
        simp [is_substable, h, nocc, ih1, ih2]
  | box ψ ih  =>
      rw [is_free] at h
      apply And.intro
      . simp [subst_svar, ih, h]
      . intro nocc
        rw [occurs] at nocc
        simp [is_substable, ih, nocc, h]
  | bind z ψ ih =>
      apply And.intro
      . by_cases heq : x = z
        . rw [←heq, subst_svar, if_pos (Eq.refl x)]
        . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
          Ne.symm heq, false_or] at h
          simp [subst_svar, heq, ih, h]
      . intro nocc
        rw [occurs] at nocc
        simp [is_substable, notoccurs_notfree, nocc]
  | _   =>
      simp [subst_svar, is_substable]

  lemma rereplacement (φ : Form N) (x y : SVAR) (h1 : occurs y φ = false) (h2 : is_substable φ y x) : (is_substable (φ[y // x]) x y) ∧ φ[y // x][x // y] = φ := by
    induction φ with
    | svar z =>
        simp [occurs] at h1
        by_cases xz : x = z
        repeat simp [subst_svar, xz, h1, is_substable]
    | impl ψ χ ih1 ih2 =>
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1
        simp only [is_substable, Bool.and_eq_true] at h2
        simp [subst_svar, ih1, ih2, h1, h2, is_substable]
    | box ψ ih =>
        simp only [occurs] at h1
        simp only [is_substable] at h2
        simp [subst_svar, ih, h1, h2, is_substable]
    | bind z ψ ih =>
        by_cases yz : y = z
        . rw [←yz]
          rw [←yz] at h1

          simp only [is_substable, beq_iff_eq, ←yz, bne_self_eq_false, Bool.false_and, ite_eq_left_iff,
            Bool.not_eq_false, implication_disjunction, Bool.not_eq_true, or_false] at h2
          have h2 := @preserve_notfree N ψ x y h2
          simp [subst_notfree_var, h2]

          have := @subst_notfree_var N (all y, ψ) y x (notoccurs_notfree h1)
          simp [@subst_notfree_var N (all y, ψ) y x, notoccurs_notfree, h1]
        . by_cases xz : x = z
          . have : is_free x (all x, ψ) = false := by simp [is_free]
            rw [←xz] at h1
            simp [←xz, subst_notfree_var, this, notoccurs_notfree, h1]
          . simp only [occurs] at h1
            simp [subst_svar, xz, yz]
            by_cases xfree : is_free x ψ
            . simp [is_substable, xfree, Ne.symm yz, bne] at h2
              simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
            . rw [show (¬is_free x ψ = true ↔ is_free x ψ = false) by simp] at xfree
              simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
    | _     =>
        apply And.intro
        repeat rfl

lemma subst_self_is_self (φ : Form N) (x : SVAR) : φ [x // x] = φ := by
  induction φ with
  | svar y   =>
      by_cases xy : x = y
      . rw [subst_svar, if_pos xy, xy]
      . rw [subst_svar, if_neg xy]
  | impl φ ψ ih1 ih2 =>
      rw [subst_svar, ih1, ih2]
  | box  φ ih  =>
      rw [subst_svar, ih]
  | bind y φ ih =>
      by_cases xy : x = y
      . rw [subst_svar, if_pos xy]
      . rw [subst_svar, if_neg xy, ih]
  | _        => rfl

lemma pos_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_pos m (v⋀φ))[i//v] = iterate_pos m (i⋀φ[i//v]) := by
  induction m with
  | zero =>
      simp [iterate_pos, iterate_pos.loop, subst_nom]
  | succ n ih =>
      simp [iterate_pos, iterate_pos.loop, subst_nom] at ih ⊢
      rw [ih]

lemma nec_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_nec m (v⟶φ))[i//v] = iterate_nec m (i⟶φ[i//v]) := by
  induction m with
  | zero =>
      simp [iterate_nec, iterate_nec.loop, subst_nom]
  | succ n ih =>
      simp [iterate_nec, iterate_nec.loop, subst_nom] at ih ⊢
      rw [ih]
