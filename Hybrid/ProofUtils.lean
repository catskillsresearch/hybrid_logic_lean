import Hybrid.Substitutions
import Hybrid.Proof
import Hybrid.ListUtils
open Classical

set_option linter.docPrime false

def iff_mp (h : ⊢ (φ ⟷ ψ)) : ⊢ (φ ⟶ ψ) :=
  Proof.mp (Proof.tautology conj_elim_l) h

def iff_mpr (h : ⊢ (φ ⟷ ψ)) : ⊢ (ψ ⟶ φ) :=
  Proof.mp (Proof.tautology conj_elim_r) h

theorem hs_taut : Proof.tautology ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) :=
  fun e => by
    sorry

theorem hs (h1 : ⊢ (φ ⟶ ψ)) (h2 : ⊢ (ψ ⟶ χ)) : ⊢ (φ ⟶ χ) :=
  Proof.mp (Proof.mp (Proof.tautology hs_taut) h1) h2

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

theorem rename_bound {φ : Form N} (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((all x, φ) ⟷ all y, φ[y // x]) := by
  rw [Form.iff]
  apply Proof.mp
  . apply Proof.mp
    . apply Proof.tautology
      apply conj_intro
    . have l1 := ax_q2_svar φ x y h2
      have l2 := general y l1
      have l3 := ax_q1 (all x, φ) (φ[y // x]) (notoccurs_notfree h1)
      have l4 := Proof.mp l3 l2
      exact l4
  . have ⟨resubst, reid⟩ := rereplacement φ x y h1 h2
    have l1 := ax_q2_svar (φ[y//x]) y x resubst
    rw [reid] at l1
    have l3 := general x l1
    by_cases xy : x = y
    . rw [←xy] at h1
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst N φ x y h1))
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := Proof.mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst N φ x y xy)
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := Proof.mp l4 l3
      exact l5

theorem rename_bound_ex (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((ex x, φ) ⟷ ex y, φ[y // x]) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply Proof.mp
  . apply Proof.mp
    . apply Proof.tautology
      apply iff_elim_l
    . apply Proof.tautology
      apply iff_not
  .
    apply rename_bound
    repeat { simp [occurs, is_substable]; assumption }

theorem conj_idempotent {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) : e.f (conjunction Γ L) ∧ e.f φ ↔ e.f (conjunction Γ L) := by
  induction L with
  | nil => simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . have := Eq.symm ((beq_iff_eq h.val φ).mp eq)
        simp only [conjunction, e_conj, this, conj_comm, and_self_left]
      . simp [elem', show (h.val == φ) = false by simp [eq]] at hyp
        simp only [conjunction, e_conj, and_assoc, ih hyp]

-- Instead of proving conjunction is associative, commutative and idempotent, we do 3-in-1:
theorem conj_helper {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) : e.f (conjunction Γ (filter' L φ)⋀φ) = true ↔ e.f (conjunction Γ L) = true := by
  induction L with
  | nil         =>
      simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . simp only [filter', eq, conjunction]
        have := (beq_iff_eq h.val φ).mp (Eq.symm eq)
        rw [this]
        by_cases phi_in_t : elem' t φ
        . conv => rhs; rw [e_conj, and_comm, conj_idempotent phi_in_t]
          simp only [ih, phi_in_t]
        . simp only [filter'_doesnt_filter, phi_in_t, e_conj, and_comm]
      . simp [elem', eq] at hyp
        simp only [hyp, e_conj, conj_comm, forall_true_left] at ih
        rw [and_comm] at ih
        simp only [filter', eq, conjunction, e_conj, and_assoc, ih]

theorem deduction_helper {Γ : Set (Form N)} (L : List Γ) (φ ψ : Form N) (h : elem' L φ) :
  Proof.tautology ((conjunction Γ L ⟶ ψ) ⟶ (conjunction Γ (filter' L φ) ⟶ φ ⟶ ψ)) := by
  intro e
  rw [e_impl, e_impl, e_impl, e_impl]
  intro h1 h2 h3
  have l1 := (@e_conj N (conjunction Γ (filter' L φ)) φ e).mpr ⟨h2, h3⟩
  rw [conj_helper h] at l1
  exact h1 l1


-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
theorem Deduction {Γ : Set (Form N)} : Γ ⊢ (ψ ⟶ φ) iff (Γ ∪ {ψ}) ⊢ φ := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hpf⟩ =>
        have l1 := Proof.mp (Proof.tautology com12) hpf
        have l2 := Proof.mp (Proof.tautology imp) l1
        have pfmem : ψ ∈ Γ ∪ {ψ} := by simp
        let L' : List ↑(Γ ∪ {ψ}) := ⟨ψ, pfmem⟩ :: list_convert L
        rw [conj_incl] at l2
        exact ⟨L', l2⟩
  . intro h
    match h with
    | ⟨L', hpf⟩ =>
      have t_ax1 := Proof.tautology (@ax_1 N (conjunction (Γ ∪ {ψ}) L'⟶φ) ψ)
      have l1 := Proof.mp t_ax1 hpf
      have l2 := Proof.mp (Proof.tautology com12) l1
      by_cases elem : elem' L' ψ
      . have t_help := Proof.tautology (deduction_helper L' ψ (ψ⟶φ) elem)
        have l3 := Proof.mp t_help l2
        have l4 := Proof.mp (Proof.tautology idem) l3
        have not_elem_L' := eq_false_of_ne_true (@filter'_filters N Γ ψ L')
        let L : List Γ := list_convert_rev (filter' L' ψ) not_elem_L'
        rw [conj_incl_rev (filter' L' ψ) not_elem_L'] at l4
        exact ⟨L, l4⟩
      . have elem : elem' L' ψ = false := by simp only [elem]
        let L : List Γ := list_convert_rev L' elem
        rw [conj_incl_rev L' elem] at l2
        exact ⟨L, l2⟩

lemma increasing_consequence (h1 : Γ ⊢ φ) (h2 : Γ ⊆ Δ) : Δ ⊢ φ := by
  simp [SyntacticConsequence] at h1 ⊢
  let ⟨L, pf⟩ := h1
  clear h1
  let L' := list_convert_general h2 L
  exists L'
  rw [conj_incl_general h2 L] at pf
  exact pf

theorem Γ_empty {φ : Form N} : ∅ ⊢ φ iff ⊢ φ := by
  unfold SyntacticConsequence
  apply TypeIff.intro
  . intro pf
    have ⟨L, pf⟩ := pf
    have := empty_list L
    simp [this, conjunction] at pf
    apply mp
    . have : ⊢(((⊥⟶⊥)⟶φ)⟶φ) := by
        apply Proof.tautology
        apply imp_taut
        eval
      exact this
    . exact pf
  . intro pf
    let L : List ↑{x : Form N | False} := []
    exists L
    simp [conjunction]
    apply mp
    . apply Proof.tautology
      apply ax_1
    . exact pf

theorem Γ_theorem : ⊢ φ → (∀ Γ, Γ ⊢ φ) := by
  intro h Γ
  apply increasing_consequence
  apply Γ_empty.mpr h
  simp

theorem Γ_theorem_rev : (∀ Γ, Γ ⊢ φ) → ⊢ φ := by
  intro h
  apply Γ_empty.mp
  apply h

theorem Γ_theorem_iff : ⊢ φ iff (∀ Γ, Γ ⊢ φ) := by
  apply TypeIff.intro <;> first | apply Γ_theorem | apply Γ_theorem_rev

theorem Γ_premise : φ ∈ Γ → Γ ⊢ φ := by
  intro mem
  have : Γ = Γ ∪ {φ} := by simp [mem]
  rw [this]
  apply Deduction.mp
  apply Γ_theorem
  apply Proof.tautology
  eval

theorem Γ_mp_helper1 {Γ : Set (Form N)} {φ ψ χ : Form N} : (Γ ⊢ ((φ ⋀ ψ) ⟶ χ)) iff ((Γ ∪ {φ}) ⊢ (ψ ⟶ χ)) := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (Proof.tautology exp)
        have l2 : Γ ⊢ (φ ⟶ ψ ⟶ χ) := ⟨L, l1⟩
        have l3 := Deduction.mp l2
        exact l3
  . intro h
    have h := Deduction.mpr h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (Proof.tautology imp)
        have l2 : Γ ⊢ (φ ⋀ ψ ⟶ χ) := ⟨L, l1⟩
        exact l2

theorem Γ_mp_helper2 {Γ : Set (Form N)} {L : List Γ} (h : Γ⊢(conjunction Γ L⟶ψ)) : Γ ⊢ ψ := by
  induction L with
  | nil =>
      rw [conjunction] at h
      have ⟨L, hL⟩ := h
      have l1 := Proof.mp (Proof.tautology com12) hL
      have l2 := Proof.mp (Proof.tautology (imp_taut imp_refl)) l1
      exists L
  | cons head tail ih =>
      have h := Γ_mp_helper1.mp h
      have : (Γ ∪ {↑head}) = Γ := by simp [head.2]
      rw [this] at h
      exact ih h

theorem Γ_mp (h1: Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ φ) : Γ ⊢ ψ := by
  match h1 with
  | ⟨L1, hL1⟩ =>
    match h2 with
    | ⟨L2, hL2⟩ =>
        have := Proof.mp (mp (Proof.tautology mp_help) hL1) hL2
        have : Γ ⊢ (conjunction Γ L2⟶ψ) := ⟨L1, this⟩
        exact Γ_mp_helper2 this

theorem Γ_neg_intro {φ : Form N} (h1 : Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ (φ ⟶ ∼ψ)) : Γ ⊢ (∼φ) := by
  have l1 := Proof.tautology (@neg_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_neg_elim {φ : Form N} {φ : Form N} (h : Γ ⊢ (∼∼φ)) : Γ ⊢ φ := by
  have l1 := Proof.tautology (@dne N φ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_conj_intro {φ : Form N} (h1 : Γ ⊢ φ) (h2 : Γ ⊢ ψ) : Γ ⊢ (φ ⋀ ψ) := by
  have l1 := Proof.tautology (@conj_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

theorem Γ_conj_elim_l {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ φ := by
  have l1 := Proof.tautology (@conj_elim_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_conj_elim_r {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ ψ := by
  have l1 := Proof.tautology (@conj_elim_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

theorem Γ_disj_intro_l {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (φ ⋁ ψ) := by
  have l1 := Proof.tautology (@disj_intro_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_intro_r {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (ψ ⋁ φ) := by
  have l1 := Proof.tautology (@disj_intro_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

theorem Γ_disj_elim {φ : Form N} (h1 : Γ ⊢ (φ ⋁ ψ)) (h2 : Γ ⊢ (φ ⟶ χ)) (h3 : Γ ⊢ (ψ ⟶ χ)) : Γ ⊢ χ := by
  have l1 := Proof.tautology (@disj_elim N φ ψ χ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  have l5 := Γ_mp l4 h3
  exact l5

lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
  induction L with
  | nil         =>
      simp only [conjunction, is_free]
  | cons h t ih =>
      simp only [is_free, Bool.or_false, Bool.or_eq_false_eq_eq_false_and_eq_false]
      apply And.intro
      . exact hyp h
      . exact ih

theorem Γ_univ_intro {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) (h2 : occurs y φ = false) (h3 : is_substable φ y x) : Γ ⊢ φ → Γ ⊢ (all y, φ[y // x]) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := Proof.mp l3 l2
      have l5 := iff_mp (rename_bound h2 h3)
      have l6 := hs l4 l5
      exact ⟨L, l6⟩

theorem Γ_univ_intro' {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) : Γ ⊢ φ → Γ ⊢ (all x, φ) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := Proof.mp l3 l2
      exists L

theorem dn_equiv_premise {φ : Form N} : Γ ⊢ (∼∼φ) iff Γ ⊢ φ := by
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

theorem ax_nom_instance {φ : Form N} (i : NOM N) (m n : ℕ) : ⊢ (iterate_pos m (i ⋀ φ) ⟶ iterate_nec n (i ⟶ φ)) := by
  let x := φ.new_var
  have x_geq : x ≥ φ.new_var := by simp [SVAR.le]
  have l1 := @ax_nom N (φ[x//i]) x m n
  have l2 := ax_q2_nom (iterate_pos m (x⋀(φ[x//i]))⟶iterate_nec n (x⟶(φ[x//i]))) x i
  have l3 := Proof.mp l2 l1
  clear l1 l2
  rw [subst_nom, pos_subst, nec_subst, nom_svar_rereplacement x_geq] at l3
  exact l3

theorem ax_q2_svar_instance : ⊢ ((all x, φ) ⟶ φ) := by
  have : φ.new_var ≥ φ.new_var := by simp [SVAR.le]
  apply hs
  apply mp
  . apply Proof.tautology
    apply iff_elim_l
  apply rename_bound
  apply new_var_is_new
  apply new_var_subst''
  assumption
  have ⟨l, r⟩ := (rereplacement φ x (φ.new_var) new_var_is_new (new_var_subst'' this))
  conv => rhs; rhs; rw [←r]
  apply ax_q2_svar
  assumption

theorem Γ_univ_elim (h : Γ ⊢ (all x, φ)) : Γ ⊢ φ := by
  exact Γ_mp (Γ_theorem ax_q2_svar_instance Γ) h

theorem rename_var (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ φ iff ⊢ (φ[y // x]) := by
  apply TypeIff.intro
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact y
    apply mp
    . apply mp
      apply Proof.tautology
      apply iff_elim_l
      apply rename_bound
      repeat assumption
    . apply general
      assumption
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact x
    apply mp
    . apply mp
      apply Proof.tautology
      apply iff_elim_r
      apply rename_bound
      repeat assumption
    . apply general
      assumption

theorem ax_q2_contrap {i : NOM N} {x : SVAR} : ⊢ (φ[i//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply Proof.tautology
    apply dni
  . apply mp
    apply Proof.tautology
    apply contrapositive
    apply ax_q2_nom

theorem ax_q2_svar_contrap {x y : SVAR} (h : is_substable φ y x) : ⊢ (φ[y//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply Proof.tautology
    apply dni
  . apply mp
    apply Proof.tautology
    apply contrapositive
    apply ax_q2_svar
    simp [is_substable]
    exact h

theorem ax_nom_instance' (x : SVAR) (m n : ℕ) : ⊢ (iterate_pos m (x ⋀ φ) ⟶ iterate_nec n (x ⟶ φ)) := by
  apply mp
  apply ax_q2_svar_instance
  assumption
  apply ax_nom

-- Lemma 3.6.1
lemma b361 {φ : Form N} : ⊢ ((φ ⟶ ex x, ψ) ⟶ ex x, (φ ⟶ ψ)) := by
  apply mp
  . apply Proof.tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {∼(ex x, φ⟶ψ)}
    have l1 : Γ ⊢ (∼(ex x, φ⟶ψ)) := by apply Γ_premise; simp
    rw [Form.bind_dual] at l1
    have l2 := Γ_theorem (Proof.tautology (@dne N (all x, ∼(φ⟶ψ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⟶ψ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (Proof.tautology (taut_iff_mp (@imp_neg N φ ψ))) Γ
    have l7 := Γ_mp l6 l5
    have l8 := Γ_conj_elim_l l7
    have l9 := Γ_conj_elim_r l7
    have l10 : Γ ⊢ (∼(ex x, ψ)) := by
      rw [Form.bind_dual]
      apply Γ_mp; apply Γ_theorem; apply Proof.tautology; apply dni
      apply Γ_univ_intro'
      . simp [is_free, -implication_disjunction]
      . exact l9
    have l11 := Γ_conj_intro l8 l10
    have l12 := Γ_mp (Γ_theorem (Proof.tautology (taut_iff_mpr (@imp_neg N φ (ex x, ψ)))) Γ) l11
    exact l12

-- Lemma 3.6.2
lemma b362 {φ : Form N} (h : is_free x φ = false) : ⊢ ((φ ⋀ ex x, ψ) ⟶ ex x, (φ ⋀ ψ)) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply Proof.tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) :=  {∼∼(all x, ∼(φ⋀ψ))}
    have l1 : Γ ⊢ (all x, ∼(φ⋀ψ)) := by
      apply Γ_mp; apply Γ_theorem; apply Proof.tautology; apply dne
      apply Γ_premise; simp
    have l2 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⋀ψ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_mp (Γ_theorem (Proof.tautology (taut_iff_mpr (@neg_conj N φ ψ))) Γ) l3
    have l5 : Γ⊢ (all x, (φ⟶∼ψ)) := by
      apply Γ_univ_intro'
      simp [is_free, -implication_disjunction]
      exact l4
    have l6 := Deduction.mp (Γ_mp (Γ_theorem (ax_q1 φ (∼ψ) h) Γ) l5)
    have l7 := Deduction.mpr (Γ_mp (Γ_theorem (Proof.tautology (@dni N (all x, ∼ψ))) (Γ ∪ {φ})) l6)
    have l8 := Γ_mp (Γ_theorem (Proof.tautology (taut_iff_mp (@neg_conj N φ (∼(all x, ∼ψ))))) Γ) l7
    exact l8

lemma ex_conj_comm {φ : Form N} : ⊢ ((ex x, (φ ⋀ ψ)) ⟶ (ex x, (ψ ⋀ φ))) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply Proof.tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {∼∼(all x, ∼(ψ⋀φ))}
    have l1 : Γ ⊢ (∼∼(all x, ∼(ψ⋀φ))) := by apply Γ_premise; simp
    have l2 := Γ_theorem (Proof.tautology (@dne N (all x, ∼(ψ⋀φ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(ψ⋀φ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (Proof.tautology (@conj_comm_t' N ψ φ)) Γ
    have l7 := Γ_mp l6 l5
    have l8 : Γ⊢(all x, ∼(φ⋀ψ)) := by
      apply Γ_univ_intro'
      simp [is_free, -implication_disjunction]
      exact l7
    have l9 := Γ_theorem (Proof.tautology (@dni N (all x, ∼(φ⋀ψ)))) Γ
    have l10 := Γ_mp l9 l8
    exact l10

lemma b362' {φ : Form N} (h : is_free x φ = false) : ⊢ (((ex x, ψ) ⋀ φ) ⟶ ex x, (ψ ⋀ φ)) := by
  have l1 := Proof.tautology (@conj_comm_t N (ex x, ψ) φ)
  have l2 := @b362 N x ψ φ h
  have l3 := hs l2 ex_conj_comm
  have l4 := hs l1 l3
  exact l4

-- Lemma 3.6.3
lemma b363  {φ : Form N} : ⊢ ((all x, (φ ⟶ ψ)) ⟶ ((all x, φ) ⟶ (all x, ψ))) := by
  let Γ : Set (Form N) := ∅ ∪ {all x, φ⟶ψ} ∪ {all x, φ}
  have l1 : Γ ⊢ (all x, (φ ⟶ ψ)) := by apply Γ_premise; simp
  have l2 : Γ⊢(φ⟶ψ) := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l1
  have l3 : Γ⊢(all x, φ) := by apply Γ_premise; simp
  have l4 : Γ⊢φ := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l3
  have l5 : ⊢((all x, φ⟶ψ)⟶((all x, φ) ⟶ ψ)) := by
    apply Γ_empty.mp; apply Deduction.mpr; apply Deduction.mpr
    apply Γ_mp
    repeat assumption
  have l6 := general x l5
  have : is_free x (all x, φ⟶ψ) = false := by simp [is_free]
  have l7 := @ax_q1 N (all x, φ⟶ψ) ((all x, φ)⟶ψ) x this
  have l8 := Proof.mp l7 l6
  have : is_free x (all x, φ) = false := by simp [is_free]
  have l9 := @ax_q1 N (all x, φ) ψ x this
  have l10 := hs l8 l9
  exact l10

theorem dn_nec : ⊢ (□ φ ⟷ □ ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply Proof.tautology
  apply conj_intro
  repeat (
    apply mp
    apply ax_k
    apply necess
    apply Proof.tautology
    first | apply dni | apply dne
  )

theorem dn_all : ⊢ ((all x, φ) ⟷ all x, ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply Proof.tautology
  apply conj_intro
  repeat (
    apply mp
    apply b363
    apply general
    apply Proof.tautology
    first | apply dni | apply dne
  )

lemma bind_dual : ⊢((all x, ψ)⟷∼(ex x, ∼ψ)) := by
    rw [Form.bind_dual]
    apply mp; apply mp
    apply Proof.tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply Proof.tautology
        apply iff_elim_l
        apply dn_all
      . apply Proof.tautology
        apply dni
    . apply hs
      . apply Proof.tautology
        apply dne
      . apply mp
        apply Proof.tautology
        apply iff_elim_r
        apply dn_all

lemma nec_dual : ⊢((□ ψ)⟷∼(◇ ∼ψ)) := by
    rw [Form.diamond]
    apply mp; apply mp
    apply Proof.tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply Proof.tautology
        apply iff_elim_l
        apply dn_nec
      . apply Proof.tautology
        apply dni
    . apply hs
      . apply Proof.tautology
        apply dne
      . apply mp
        apply Proof.tautology
        apply iff_elim_r
        apply dn_nec

lemma diw_impl (h : ⊢(φ ⟶ ψ)) : ⊢ (◇φ ⟶ ◇ψ) := by
  have l1 := Proof.mp (Proof.tautology contrapositive) h
  have l2 := necess l1
  have l3 := Proof.mp ax_k l2
  have l4 := Proof.mp (Proof.tautology contrapositive) l3
  exact l4

lemma ax_brcn_contrap {φ : Form N} : ⊢ ((◇ ex x, φ) ⟶ (ex x, ◇ φ)) := by
  simp only [Form.diamond, Form.bind_dual]
  apply mp
  . apply Proof.tautology
    apply contrapositive
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.union_singleton, insert_emptyc_eq]
    let Γ : Set (Form N) := {all x, ∼∼(□∼φ)}
    have l1 : Γ ⊢ (all x, ∼∼(□∼φ)) := by apply Γ_premise; simp
    have l2 := Γ_theorem (mp (Proof.tautology iff_elim_r) (@dn_all x N (□∼φ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_brcn N (∼φ) x) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (mp (Proof.tautology iff_elim_l) (@dn_nec N (all x, ∼φ))) Γ
    have l7 := Γ_mp l6 l5
    exact l7

theorem iff_subst : ⊢ ((φ ⟷ ψ) ⟶ (ψ ⟷ χ) ⟶ (φ ⟷ χ)) := by
  apply Proof.tautology
  sorry

theorem pf_iff_subst : ⊢ (φ ⟷ ψ) → ⊢ (ψ ⟷ χ) → ⊢ (φ ⟷ χ) := by
  intro h1 h2
  apply mp
  apply mp
  apply iff_subst
  exact ψ
  repeat assumption
