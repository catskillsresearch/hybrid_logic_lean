import Hybrid.Soundness
import Hybrid.ListUtils

variable (φ ψ: Form N)

def Form.replace_bound : Form N → SVAR → Form N
  | (all z, φ), x =>
        if z = x then
          let y := (φ.replace_bound x).new_var + x.letter + 1
          all y, (φ.replace_bound x)[y//x]
        else all z, φ.replace_bound x
  | (impl φ ψ), x => (φ.replace_bound x) ⟶ (ψ.replace_bound x)
  | (□φ), x     => □ (φ.replace_bound x)
  | φ, _        => φ

theorem replace_neg : (∼φ).replace_bound x = ∼(φ.replace_bound x) := by
  sorry

theorem replace_bound_depth {φ : Form N} {x : SVAR} : (φ.replace_bound x).depth = φ.depth := by
  sorry

theorem replace_bound_depth' {ψ : Form N} {x z : SVAR} : ((ψ.replace_bound x)[x//z]).depth < (ex x, ψ).depth := by
  rw [subst_depth', replace_bound_depth]
  apply ex_depth

theorem substable_after_replace (φ : Form N) : is_substable (φ.replace_bound y) y x := by
  induction φ with
  | bind z φ ih =>
      simp only [Form.replace_bound]
      split
      . rw [is_substable]
        split
        . simp
        . simp
          apply And.intro
          . have : (φ.replace_bound y).new_var + y.letter ≥ y := by simp [SVAR.le, SVAR.add]

            sorry
          .
            sorry
      . sorry
  | impl φ ψ ih1 ih2 => sorry
  | box φ ih => sorry
  | _ =>
      simp only [Form.replace_bound, is_substable]

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
        sorry
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
  | _        => simp only [occurs]

def rename_bound {φ : Form N} (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((all x, φ) ⟷ all y, φ[y // x]) := by
  rw [Form.iff]
  apply Proof.mp
  . apply Proof.mp
    . apply Proof.tautology
      apply conj_intro
    . have l1 := Proof.ax_q2_svar φ x y h2
      have l2 := Proof.general y l1
      have l3 := Proof.ax_q1 (all x, φ) (φ[y // x]) (notoccurs_notfree h1)
      have l4 := Proof.mp l3 l2
      exact l4
  . have ⟨resubst, reid⟩ := rereplacement φ x y h1 h2
    have l1 := Proof.ax_q2_svar (φ[y//x]) y x resubst
    rw [reid] at l1
    have l3 := Proof.general x l1
    by_cases xy : x = y
    . rw [←xy] at h1
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst N φ x y h1))
      have l4 := Proof.ax_q1 (all y, φ[y//x]) φ notf
      have l5 := Proof.mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst N φ x y xy)
      have l4 := Proof.ax_q1 (all y, φ[y//x]) φ notf
      have l5 := Proof.mp l4 l3
      exact l5

def Γ_premise : φ ∈ Γ → Γ ⊢ φ := by
  intro mem
  have : Γ = Γ ∪ {φ} := by simp [mem]
  rw [this]
  sorry

def Γ_mp (h1: Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ φ) : Γ ⊢ ψ := by
  match h1 with
  | ⟨L1, hL1⟩ =>
    match h2 with
    | ⟨L2, hL2⟩ =>
        sorry

def increasing_consequence (h1 : Γ ⊢ φ) (h2 : Γ ⊆ Δ) : Δ ⊢ φ := by
  simp [SyntacticConsequence] at h1 ⊢
  let ⟨L, pf⟩ := h1
  clear h1
  let L' := list_convert_general h2 L
  exists L'
  rw [conj_incl_general h2 L] at pf
  exact pf

def Γ_theorem : ⊢ φ → (∀ Γ, Γ ⊢ φ) := by
  intro h Γ
  apply increasing_consequence
  sorry
  sorry
  sorry

theorem hs_taut : Tautology ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) :=
  fun e => by
    sorry

def hs (h1 : ⊢ (φ ⟶ ψ)) (h2 : ⊢ (ψ ⟶ χ)) : ⊢ (φ ⟶ χ) :=
  Proof.mp (Proof.mp (Proof.tautology (@hs_taut N φ ψ χ )) h1) h2

def ax_q2_svar_instance : ⊢ ((all x, φ) ⟶ φ) := by
  have : φ.new_var ≥ φ.new_var := by simp [SVAR.le]
  apply hs
  apply Proof.mp
  . apply Proof.tautology
    apply iff_elim_l
  apply rename_bound
  apply new_var_is_new
  apply new_var_subst''
  assumption
  have ⟨l, r⟩ := (rereplacement φ x (φ.new_var) new_var_is_new (new_var_subst'' this))
  conv => rhs; rhs; rw [←r]
  apply Proof.ax_q2_svar
  assumption

def Γ_empty {φ : Form N} : ∅ ⊢ φ iff ⊢ φ := by
  unfold SyntacticConsequence
  apply TypeIff.intro
  . intro pf
    have ⟨L, pf⟩ := pf
    have := empty_list L
    simp [this, conjunction] at pf
    apply Proof.mp
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
    apply Proof.mp
    . apply Proof.tautology
      apply ax_1
    . exact pf

-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
def Deduction {Γ : Set (Form N)} : Γ ⊢ (ψ ⟶ φ) iff (Γ ∪ {ψ}) ⊢ φ := by
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
      . sorry
      . have elem : elem' L' ψ = false := by simp only [elem]
        let L : List Γ := list_convert_rev L' elem
        rw [conj_incl_rev L' elem] at l2
        exact ⟨L, l2⟩

-- Lemma 3.6.1
def b361 {φ : Form N} : ⊢ ((φ ⟶ ex x, ψ) ⟶ ex x, (φ ⟶ ψ)) := by
  apply Proof.mp
  . apply Proof.tautology
    apply contrapositive'
  . sorry

def ex_conj_comm {φ : Form N} : ⊢ ((ex x, (φ ⋀ ψ)) ⟶ (ex x, (ψ ⋀ φ))) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply Proof.mp
  . apply Proof.tautology
    apply contrapositive'
  . apply Γ_empty.mp
    sorry

-- Lemma 3.6.2
def b362 {φ : Form N} (h : is_free x φ = false) : ⊢ ((φ ⋀ ex x, ψ) ⟶ ex x, (φ ⋀ ψ)) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply Proof.mp
  . apply Proof.tautology
    apply contrapositive'
  . sorry

def b362' {φ : Form N} (h : is_free x φ = false) : ⊢ (((ex x, ψ) ⋀ φ) ⟶ ex x, (ψ ⋀ φ)) := by
  have l1 := Proof.tautology (@conj_comm_t N (ex x, ψ) φ)
  sorry

-- Lemma 3.6.3
def b363  {φ : Form N} : ⊢ ((all x, (φ ⟶ ψ)) ⟶ ((all x, φ) ⟶ (all x, ψ))) := by
  let Γ : Set (Form N) := ∅ ∪ {all x, φ⟶ψ} ∪ {all x, φ}
  have l1 : Γ ⊢ (all x, (φ ⟶ ψ)) := by apply Γ_premise; sorry
  have l2 : Γ⊢(φ⟶ψ) := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l1
  have l3 : Γ⊢(all x, φ) := by apply Γ_premise; sorry
  have l4 : Γ⊢φ := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l3
  have l5 : ⊢((all x, φ⟶ψ)⟶((all x, φ) ⟶ ψ)) := by
    sorry
  have l6 := Proof.general x l5
  have : is_free x (all x, φ⟶ψ) = false := by simp [is_free]
  have l7 := @Proof.ax_q1 N (all x, φ⟶ψ) ((all x, φ)⟶ψ) x this
  have l8 := Proof.mp l7 l6
  have : is_free x (all x, φ) = false := by simp [is_free]
  have l9 := @Proof.ax_q1 N (all x, φ) ψ x this
  sorry

def rename_all_bound_pf (φ : Form N) (x : SVAR) : ⊢ (φ ⟷ (φ.replace_bound x)) :=
  match φ with
  | Form.bind z ψ =>
      have ih := rename_all_bound_pf ψ x
      sorry -- Fill in the proof for this case
  | Form.impl φ₁ φ₂ =>
      have ih1 := rename_all_bound_pf φ₁ x
      have ih2 := rename_all_bound_pf φ₂ x
      Proof.mp (Proof.mp (Proof.tautology iff_imp) ih1) ih2
  | Form.box ψ =>
      have ih := rename_all_bound_pf ψ x
      let l1 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_l) ih))
      let l2 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_r) ih))
      let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
      l3
  | _ =>
      sorry

theorem rename_all_bound (φ : Form N) (x : SVAR) : ⊨ (φ ⟷ (φ.replace_bound x)) := by
  exact WeakSoundness (rename_all_bound_pf φ x)
