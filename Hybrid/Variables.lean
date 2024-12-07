
import Hybrid.Form

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

lemma ge_new_var_subst_nom {i : NOM N} {y : SVAR} : φ.new_var ≥ φ[i // y].new_var := by
  induction φ <;> simp [Form.new_var, subst_nom, *] at *
  . split <;> simp [Form.new_var, SVAR.le]
  . simp [max]; split <;> split <;> simp [SVAR.le, *] at *; apply Nat.le_trans <;> assumption; apply Nat.le_of_lt; apply Nat.lt_of_le_of_lt <;> assumption
  . simp [max] at *; split <;> split <;> simp [Form.new_var, SVAR.le, SVAR.add, max] at * <;> split <;> simp [SVAR.le, SVAR.add, *] at *;
                      apply Nat.le_of_lt; apply Nat.lt_of_le_of_lt <;> assumption

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

lemma new_var_subst {φ : Form N} {i : NOM N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable (φ[y//i]) x y := by
induction φ with
| nom  j  =>
    simp [nom_subst_svar]
    split <;> simp [is_substable]
| bind z ψ ih =>
    simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
        bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Bool.not_eq_false, Bool.and_eq_true] at h ⊢
    intro _
    by_cases hc : (z + 1).letter > (Form.new_var ψ).letter
    . simp [hc] at h
      simp only [gt_iff_lt, ge_iff_le] at hc ih
      have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
      have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
      rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
      exact ⟨ne, ih⟩
    . simp [hc] at h
      simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih
      have ih := ih h
      have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
      rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
      exact ⟨ne, ih⟩
| impl ψ χ ih1 ih2 =>
    simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
    by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
    . simp [hc] at h
      have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
      exact ⟨ih1 h, ih2 this⟩
    . simp [hc] at h
      simp at hc
      have := Nat.le_trans hc h
      exact ⟨ih1 this, ih2 h⟩
| box ψ ih         =>
    simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
    exact ih h
| _  =>
    simp [is_substable]

lemma new_var_subst'' {φ : Form N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable φ x y := by
induction φ with
| bind z ψ ih =>
    simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
        bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Bool.not_eq_false, Bool.and_eq_true] at h ⊢
    intro _
    by_cases hc : (z + 1).letter > (Form.new_var ψ).letter
    . simp [hc] at h
      simp only [gt_iff_lt, ge_iff_le] at hc ih
      have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
      have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
      rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
      exact ⟨ne, ih⟩
    . simp [hc] at h
      simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih
      have ih := ih h
      have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
      rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
      exact ⟨ne, ih⟩
| impl ψ χ ih1 ih2 =>
    simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
    by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
    . simp [hc] at h
      have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
      exact ⟨ih1 h, ih2 this⟩
    . simp [hc] at h
      simp at hc
      have := Nat.le_trans hc h
      exact ⟨ih1 this, ih2 h⟩
| box ψ ih         =>
    simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
    exact ih h
| _  =>
    simp [is_substable]

lemma scz {φ : Form N} (i : NOM N) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
induction φ with
| nom a       =>
    simp [nom_subst_svar] ; split <;> simp [is_free, hy]
| bind z ψ ih =>
    simp [is_free, -implication_disjunction]
    simp [new_var_geq2 h] at ih
    simp [ih]
| impl ψ χ ih1 ih2 =>
    have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h
    simp [ih1_cond, ih2_cond] at ih1 ih2
    simp [is_free, ih1, ih2]
| box ψ ih         =>
    simp [Form.new_var] at h
    simp [h] at ih
    simp [is_free, ih]
| _ => simp [is_free]

lemma new_var_subst' {φ : Form N} (i : NOM N) {x y : SVAR} (h1 : is_substable φ v y) (h2 : x ≥ φ.new_var) (h3 : y ≠ x) : is_substable (φ[x//i]) v y := by
induction φ with
| nom  a      => simp [nom_subst_svar]; split <;> simp [is_substable]
| bind z ψ ih =>
    have xge := (new_var_geq2 h2).right
    have := @scz N x y ψ i xge h3
    simp [←this, nom_subst_svar, is_substable, -implication_disjunction]
    clear this
    intro h
    simp [is_substable, h] at h1
    simp [h1, xge, ih]
| impl ψ χ ih1 ih2  =>
    simp [is_substable] at h1
    simp [Form.new_var] at h2
    have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h2
    simp [h1, h2, ih1_cond, ih2_cond] at ih1 ih2
    simp [is_substable, ih1, ih2]
| box ψ ih          =>
    simp [is_substable] at h1
    simp [Form.new_var] at h2
    simp [h1, h2] at ih
    simp [is_substable, ih]
| _       =>  simp [nom_subst_svar, h1]

lemma nom_subst_trans (i : NOM N) (x y : SVAR) (h : y ≥ φ.new_var) : φ[y // i][x // y] = φ[x // i] := by
induction φ with
| bttm => simp [nom_subst_svar, subst_svar]
| prop => simp [nom_subst_svar, subst_svar]
| nom _ =>
  simp [nom_subst_svar]
  split <;> simp [subst_svar]
| svar z =>
  have nocc := ge_new_var_is_new h
  simp [subst_svar]
  split <;> simp [nom_subst_svar, occurs] at *; contradiction
| bind z ψ ih =>
  simp [subst_svar]
  have := new_var_geq2 h
  by_cases hc : y = z
  . exfalso
    have := this.left
    simp [hc] at this
    have := Nat.ne_of_lt (Nat.lt_succ_of_le this)
    contradiction
  . simp [nom_subst_svar, ih this.right, hc]
| impl ψ χ ih1 ih2 =>
    simp [nom_subst_svar, subst_svar, ih1, ih2, new_var_geq1 h]
| box ψ ih         =>
    simp [Form.new_var] at h
    simp [nom_subst_svar, subst_svar, ih, h]

lemma ge_new_var_subst_helpr {i : NOM N} {x : SVAR} (h : y ≥ Form.new_var (χ⟶ψ)) : y ≥ Form.new_var (χ⟶ψ[i//x]⟶⊥) := by
  simp [Form.new_var, max]
  split <;> split
  . exact (new_var_geq1 h).left
  . apply Nat.le_trans
    apply ge_new_var_subst_nom
    exact (new_var_geq1 h).right
  . exact (new_var_geq1 h).left
  . simp [SVAR.le]

lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
  induction L with
  | nil         =>
      simp only [conjunction, is_free]
  | cons h t ih =>
      simp only [is_free, Bool.or_false, Bool.or_eq_false_eq_eq_false_and_eq_false]
      apply And.intro
      . exact hyp h
      . exact ih

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

lemma notocc_beforeafter_subst {φ : Form N} {x y : SVAR} (h : occurs x φ = false) : occurs x (φ[y // x]) = false := by
  induction φ with
  | svar z   =>
      by_cases xz : x = z
      <;> simp [subst_svar, if_pos xz, xz, occurs, h] at *
  | impl _ _ ih1 ih2 =>
      simp [subst_svar, occurs, not_or, ih1, ih2, -implication_disjunction] at *
      exact ⟨ih1 h.left, ih2 h.right⟩
  | box _ ih    =>
      simp [subst_svar, occurs, ih, -implication_disjunction] at *
      exact ih h
  | bind z ψ ih =>
      by_cases xz : x = z
      . simp [subst_svar, xz, occurs] at *
        exact h
      . simp [subst_svar, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
        exact ih h
  | _        => simp only [occurs]

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

theorem Form.new_var_properties (φ : Form N) : ∃ x : SVAR, x ≥ φ.new_var ∧ occurs x φ = false ∧ (∀ y : SVAR, is_substable φ x y) := by
  exists φ.new_var
  simp [SVAR.le, new_var_is_new]
  intro
  apply new_var_subst''
  simp [SVAR.le]
