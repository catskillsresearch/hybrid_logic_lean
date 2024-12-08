import Hybrid.Nominals

theorem subst_depth {i : NOM N} {x : SVAR} {φ : Form N} : φ[i // x].depth = φ.depth := by
  induction φ <;> simp [subst_nom, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth' {x y : SVAR} {φ : Form N} : φ[y // x].depth = φ.depth := by
  induction φ <;> simp [subst_svar, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth'' {x : SVAR} {i : NOM N} {φ : Form N} : (φ[i//x]).depth < (ex x, φ).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply ex_depth

theorem iff_subst_svar {y x : SVAR} : (φ ⟷ ψ)[y // x] = (φ[y//x] ⟷ ψ[y//x]) := by
  simp [subst_svar]

lemma dbl_subst_nom {j : NOM N} {x : SVAR} (i : NOM N) (h : nom_occurs j φ = false) : φ[j//i][x//j] = φ[x//i] := by
  induction φ <;> simp [nom_occurs, nom_subst_nom, nom_subst_svar, -implication_disjunction, *] at *
  . split <;> simp [nom_subst_svar, Ne.symm h]
  repeat simp [h, *] at *

lemma svar_svar_nom_subst {i j : NOM N} {x : SVAR} (h : x ≥ φ.new_var) : φ[x//i][j//x] = φ[j//i] := by
  induction φ <;> simp [nom_subst_svar, nom_subst_nom, subst_nom, -implication_disjunction, *] at *
  . apply Ne.symm; apply diffsvar; assumption
  . split <;> simp [subst_nom]
  . simp [new_var_geq1 h, *] at *
  . simp [Form.new_var] at h
    simp [h, *] at *
  . split
    . exfalso
      have := Ne.symm (diffsvar (new_var_geq2 h).left)
      contradiction
    . simp [new_var_geq2 h, *] at *

  lemma nom_subst_self {i : NOM N} : φ[i // i] = φ := by
    induction φ <;> simp [nom_subst_nom, -implication_disjunction, *] at *
    . intro h ; apply Eq.symm; assumption

  lemma eq_new_var {i j : NOM N} : φ.new_var = (φ[i // j]).new_var := by
    induction φ <;> simp [Form.new_var, nom_subst_nom, *] at *
    . split <;> simp [Form.new_var]



  theorem odd_nom {i : NOM TotalSet} : (Form.nom i).odd_noms = Form.nom (2 * i + 1) := by
    simp [Form.odd_noms, Form.odd_list_noms, Form.list_noms, Form.bulk_subst, nom_subst_nom, NOM_eq, NOM.hmul, NOM.add, Nat.mul_comm]

  theorem bulk_subst_impl {φ ψ : Form TotalSet} : (φ ⟶ ψ).bulk_subst l₁ l₂ = φ.bulk_subst l₁ l₂ ⟶ ψ.bulk_subst l₁ l₂ := by
    sorry

  theorem list_noms_impl_r {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (φ ⟶ ψ).odd_list_noms (φ ⟶ ψ).list_noms := by
    sorry

  theorem list_noms_impl_l {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (ψ ⟶ φ).odd_list_noms (ψ ⟶ φ).list_noms := by
    sorry

  theorem odd_impl : (φ ⟶ ψ).odd_noms = φ.odd_noms ⟶ ψ.odd_noms := by
    unfold Form.odd_noms
    conv => rhs; rw [@list_noms_impl_r φ ψ, @list_noms_impl_l ψ φ]
    simp [bulk_subst_impl]

  theorem odd_box : (□φ).odd_noms = □(φ.odd_noms) := by sorry

  theorem odd_bind : (all x, φ).odd_noms = all x, (φ.odd_noms) := by sorry

  def List.to_odd {Γ : Set (Form TotalSet)} {L : List Γ} : List Γ.odd_noms := sorry

  def List.odd_to {Γ : Set (Form TotalSet)} {L : List Γ.odd_noms} : List Γ := sorry

  theorem odd_conj (Γ : Set (Form TotalSet)) (L : List Γ) : (conjunction Γ L).odd_noms = conjunction Γ.odd_noms L.to_odd := by
    sorry

  theorem odd_conj_rev (Γ : Set (Form TotalSet)) (L' : List Γ.odd_noms) : (conjunction Γ L'.odd_to).odd_noms = conjunction Γ.odd_noms L' := by
    sorry
