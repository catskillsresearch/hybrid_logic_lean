import Hybrid.Variables
import Hybrid.IteratedModalities

lemma nom_svar_subst_symm {v x y : SVAR} {i : NOM N} (h : y ≠ x) : φ[x//i][v//y] = φ[v//y][x//i] := by
  induction φ <;> simp [subst_svar, nom_subst_svar, *] at *
  . split <;> simp[nom_subst_svar]
  . split <;> simp [subst_svar, h]
  . split <;> simp [nom_subst_svar]

lemma nom_nom_subst_symm {x y : SVAR} {j i : NOM N} (h1 : j ≠ i) (h2 : y ≠ x) : φ[x//i][j//y] = φ[j//y][x//i] := by
  induction φ <;> simp [nom_subst_svar, subst_nom, *] at *
  . split <;> simp [nom_subst_svar, *]
  . split <;> simp [subst_nom, *]
  . split <;> simp [nom_subst_svar]

lemma subst_collect_all {x y : SVAR} {i : NOM N} : φ[i//y][x//i] = φ[x//i][x//y] := by
  induction φ <;> simp [subst_svar, subst_nom, nom_subst_svar, *] at *
  . split <;> simp [nom_subst_svar]
  . split <;> simp [subst_svar]
  . split <;> simp [nom_subst_svar, *]

theorem nom_subst_nocc (h : nom_occurs i χ = false) (y : SVAR) : χ[y // i] = χ := by
  induction χ <;> simp [nom_occurs, nom_subst_svar, *, -implication_disjunction] at *
  . intro; apply h; apply Eq.symm; assumption
  . simp [h] at *
    apply And.intro <;> assumption

theorem subst_collect_all_nocc (h : nom_occurs i χ = false) (x y : SVAR) : χ[i // x][y // i] = χ[y // x] := by
  rw [subst_collect_all, nom_subst_nocc h y]

lemma new_var_geq1 : x ≥ (φ ⟶ ψ).new_var → (x ≥ φ.new_var ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  sorry
  sorry

lemma new_var_geq2 : x ≥ (all y, ψ).new_var → (x ≥ (y+1) ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  sorry
  sorry

lemma nom_svar_rereplacement {φ : Form N} {i : NOM N} (h : x ≥ φ.new_var) : φ[x // i][i // x] = φ := by
  induction φ <;> simp [nom_subst_svar, subst_nom]
  . have := ge_new_var_is_new h
    simp [occurs] at this
    exact this
  . split <;> simp [subst_nom, *]
  . simp [new_var_geq1 h, *]
  . simp [new_var_geq3 h, *]
  . split
    . next h2 =>
        have l1 := (new_var_geq2 h).left
        rw [←h2] at l1
        have l2 := Nat.le_succ x
        have := Nat.le_antisymm l1 l2
        simp [SVAR.add] at this
    . simp [new_var_geq2 h, *]

lemma pos_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_pos m (v⋀φ))[x//i] = iterate_pos m (Form.svar v⋀φ[x//i]) := by
  induction m with
  | zero =>
      simp [iterate_pos, iterate_pos.loop, nom_subst_svar]
  | succ n ih =>
      simp [iterate_pos, iterate_pos.loop, nom_subst_svar] at ih ⊢
      rw [ih]

lemma nec_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_nec m (v⟶φ))[x//i] = iterate_nec m (Form.svar v⟶φ[x//i]) := by
  induction m with
  | zero =>
      simp [iterate_nec, iterate_nec.loop, nom_subst_svar]
  | succ n ih =>
      simp [iterate_nec, iterate_nec.loop, nom_subst_svar] at ih ⊢
      rw [ih]

lemma diffsvar {v x : SVAR} (h : x ≥ v+1) : v ≠ x := by
  simp; intro abs; exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self v.letter) h)) (SVAR.mk.inj abs)

-- just remove this definition, it is completely redundant...
def descending (l : List (NOM N)) : Prop :=
  match l with
  | []        =>    True
  | h :: t    =>    (∀ i ∈ t, h > i) ∧ descending t

def descending' (l : List (NOM N)) : Prop := l.Chain' GT.gt

theorem eq_len {φ : Form TotalSet} : φ.list_noms.length = φ.odd_list_noms.length := by simp [Form.odd_list_noms]

theorem odd_is_odd {φ : Form TotalSet} (h1 : n < φ.list_noms.length) (h2 : n < φ.odd_list_noms.length) : φ.odd_list_noms.get ⟨n, h2⟩ = 2 * φ.list_noms.get ⟨n, h1⟩ + 1 := by
  simp [Form.odd_list_noms, Form.list_noms]

theorem descending_equiv (l : List (NOM N)) : descending l ↔ descending' l := by
  induction l with
  | nil         =>  simp [descending, descending']
  | cons h t ih =>
      simp [descending, descending', List.Chain', List.chain_iff_pairwise, -implication_disjunction]
      intros
      simp [descending', List.chain'_iff_pairwise] at ih
      exact ih

theorem descending_property (desc : descending l) (h0 : pos < l.length) (h1 : i ∈ l) (h2 : i > l[pos]) : i ∈ l.take pos := by
  match l with
  | []     => simp at h1
  | h :: t =>
      simp at h0 h1
      cases pos with
      | zero =>
          simp at h2 ⊢
          apply Or.elim h1
          . intro eq
            rw [eq] at h2
            apply Nat.lt_irrefl h.letter
            assumption
          . intro i_mem_t
            apply Nat.lt_asymm h2
            exact (desc.left i i_mem_t)
      | succ pos =>
          apply Or.elim h1
          . intro i_h
            simp [i_h]
          . intro h1_new
            simp
            apply Or.inr
            have desc_new := desc.right
            have h0_new : pos < t.length := by apply Nat.lt_of_succ_lt_succ; assumption
            have h2_new : i > t[pos] := by simp at h2 ⊢; simp [h2]
            exact descending_property desc_new h0_new h1_new h2_new

theorem descending_ndup (desc : descending l) (h0 : pos < l.length) (h1 : i = l[pos]) : ¬i ∈ l.take pos := by
  match l with
  | []      => simp
  | h :: t  =>
      let fin_pos : Fin (h::t).length := ⟨pos, h0⟩
      simp only [descending_equiv, descending', List.chain'_iff_pairwise, List.pairwise_iff_get] at desc

      intro habs
      have ⟨n, is_i⟩ := List.mem_iff_get.mp habs
      have n_lt := n.2
      simp only [List.length_take, ge_iff_le, lt_min_iff] at n_lt
      sorry

theorem descending_list_noms {φ : Form TotalSet} : descending φ.list_noms := by
  rw [descending_equiv, descending']
  exact list_noms_chain'

theorem descending_odd_list_noms {φ : Form TotalSet} : descending φ.odd_list_noms := by
  have dln := @descending_list_noms φ
  have : ∀ a b : NOM TotalSet, (2 * b + 1 < 2 * a + 1) ↔ (b < a) := by simp [NOM.lt, NOM.add, NOM.hmul]
  have := @List.Pairwise.iff (NOM TotalSet) (fun a b => 2 * b + 1 < 2 * a + 1) (fun a b => b < a) this
  simp only [Form.odd_list_noms, descending_equiv, descending', List.chain'_iff_pairwise, List.pairwise_map, GT.gt, this] at dln ⊢
  assumption

theorem occurs_list_noms : nom_occurs i φ ↔ i ∈ φ.list_noms := by
  induction φ with
  | impl φ ψ ih1 ih2 =>
      simp [Form.list_noms, nom_occurs, ih1, ih2]
      rw [←List.mem_append]
      sorry
  | box _ ih    => exact ih
  | bind _ _ ih => exact ih
  | _        => simp [Form.list_noms, nom_occurs]

theorem list_noms_subst {old new : NOM N} : i ∈ (φ[new // old]).list_noms → ((i ∈ φ.list_noms ∧ i ≠ old) ∨ i = new) := by
  rw [←occurs_list_noms, ←occurs_list_noms]
  intro h
  induction φ with
  | nom j =>
      simp [nom_subst_nom] at h
      split at h
      . simp [nom_occurs] at h; apply Or.inr; assumption
      . apply Or.inl
        apply And.intro
        . assumption
        . simp [nom_occurs] at h
          rw [h]
          assumption
  | impl ψ χ ih1 ih2 =>
      simp [nom_occurs] at h ⊢
      apply Or.elim h
      . intro hyp
        apply Or.elim (ih1 hyp)
        . intro hl
          simp [hl]
        . intro hr
          simp [hr]
      . intro hyp
        apply Or.elim (ih2 hyp)
        . intro hl
          simp [hl]
        . intro hr
          simp [hr]
  | box ψ ih =>
      simp [nom_occurs] at h
      exact ih h
  | bind _ ψ ih =>
      simp [nom_occurs] at h
      exact ih h
  | _     => simp [nom_occurs] at h

theorem occ_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : nom_occurs i (φ.bulk_subst l_new l_old) → ((i ∈ φ.list_noms ∧ i ∉ l_old) ∨ i ∈ l_new) := by
  intro h
  induction l_new generalizing φ l_old with
  | nil => cases l_old <;> simp [Form.bulk_subst] at *; repeat exact occurs_list_noms.mp h
  | cons h_new t_new ih =>
      cases l_old with
      | nil =>
          simp [Form.bulk_subst] at h ⊢
          apply Or.inl
          exact occurs_list_noms.mp h
      | cons h_old t_old =>
          simp [Form.bulk_subst] at eq_len h ⊢
          have := ih eq_len h
          apply Or.elim this
          . intro hyp
            clear this ih
            cases t_new
            . have := List.length_eq_zero.mp (Eq.symm (Eq.subst eq_len (@List.length_nil (NOM N))))
              simp [this, Form.bulk_subst] at h ⊢
              apply Or.elim (list_noms_subst (occurs_list_noms.mp h))
              . intro c1
                simp [c1]
              . intro c2
                exact Or.inr c2
            . cases t_old
              . simp at eq_len
              . simp [Form.bulk_subst] at hyp ⊢
                have ⟨a, b⟩ := hyp
                apply Or.elim (list_noms_subst b)
                . intro c1
                  apply Or.inl
                  simp [c1, a]
                . intro c2
                  simp [c2]
          . intro hyp
            clear this ih
            apply Or.inr
            apply Or.inr
            assumption

theorem nocc_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : ((i ∉ φ.list_noms ∨ i ∈ l_old) ∧ i ∉ l_new) → nom_occurs i (φ.bulk_subst l_new l_old) = false := by
  rw [contraposition]
  simp [-implication_disjunction]
  intro h1 h2
  apply Or.elim (occ_bulk eq_len h1)
  . simp
  . simp [h2]

theorem has_nocc_bulk_property : ∀ φ : Form TotalSet, nocc_bulk_property φ.odd_list_noms φ.list_noms φ := by
  unfold nocc_bulk_property
  intro φ n i h
  sorry

theorem nocc_bulk_property_induction : nocc_bulk_property (h_new :: t_new) (h_old :: t_old) φ → nocc_bulk_property t_new t_old (φ[h_new//h_old]) := by
  unfold nocc_bulk_property
  intro h n i eq_i
  let m : Fin (List.length (h_new :: t_new)) := ⟨n.val+1, Nat.succ_lt_succ_iff.mpr n.2⟩
  have m_n : m.val = n.val + 1 := by simp
  sorry

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
    sorry
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
