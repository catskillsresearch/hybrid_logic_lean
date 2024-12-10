import Hybrid.ListUtils
import Hybrid.RenameBound
open Classical

set_option linter.docPrime false

variable (N : Set ℕ)

variable (φ ψ χ : Form N)

def iff_mp (h : ⊢ (φ ⟷ ψ)) : ⊢ (φ ⟶ ψ) :=
  Proof.mp (Proof.tautology conj_elim_l) h

def iff_mpr (h : ⊢ (φ ⟷ ψ)) : ⊢ (ψ ⟶ φ) :=
  Proof.mp (Proof.tautology conj_elim_r) h

theorem conj_idempotent [inst: BEq (Form N)] [inst1: LawfulBEq (Form N)]
                        {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) :
                        e.f (conjunction Γ L) ∧ e.f φ ↔ e.f (conjunction Γ L) := by
  induction L with
  | nil => simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . sorry
      . sorry

-- Instead of proving conjunction is associative, commutative and idempotent, we do 3-in-1:
theorem conj_helper {e : Eval N} {Γ : Set (Form N)} {L : List Γ} (hyp : elem' L φ) : e.f (conjunction Γ (filter' L φ)⋀φ) = true ↔ e.f (conjunction Γ L) = true := by
  induction L with
  | nil         =>
      simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == φ
      . simp only [filter', eq, conjunction]
        sorry
      . simp [elem', eq] at hyp
        simp only [hyp, e_conj, conj_comm, forall_true_left] at ih
        rw [and_comm] at ih
        simp only [filter', eq, conjunction, e_conj, and_assoc, ih]

theorem deduction_helper {Γ : Set (Form N)} (L : List Γ) (φ ψ : Form N) (h : elem' L φ) :
                Tautology ((conjunction Γ L ⟶ ψ) ⟶ (conjunction Γ (filter' L φ) ⟶ φ ⟶ ψ)) := by
  intro e
  rw [e_impl, e_impl, e_impl, e_impl]
  intro h1 h2 h3
  have l1 := (@e_conj N (conjunction Γ (filter' L φ)) φ e).mpr ⟨h2, h3⟩
  sorry

def Γ_theorem_rev : (∀ Γ, Γ ⊢ φ) → ⊢ φ := by
  intro h
  sorry

def Γ_theorem_iff : ⊢ φ iff (∀ Γ, Γ ⊢ φ) := by
  apply TypeIff.intro <;> first | apply Γ_theorem | apply Γ_theorem_rev


def Γ_mp_helper1 {Γ : Set (Form N)} {φ ψ χ : Form N} : (Γ ⊢ ((φ ⋀ ψ) ⟶ χ)) iff ((Γ ∪ {φ}) ⊢ (ψ ⟶ χ)) := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hL⟩ =>
        sorry
  . intro h
    sorry

def Γ_mp_helper2 {Γ : Set (Form N)} {L : List Γ} (h : Γ⊢(conjunction Γ L⟶ψ)) : Γ ⊢ ψ := by
  induction L with
  | nil =>
      rw [conjunction] at h
      have ⟨L, hL⟩ := h
      have l1 := Proof.mp (Proof.tautology com12) hL
      have l2 := Proof.mp (Proof.tautology (imp_taut imp_refl)) l1
      exists L
  | cons head tail ih =>
      sorry

def Γ_neg_intro {φ : Form N} (h1 : Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ (φ ⟶ ∼ψ)) : Γ ⊢ (∼φ) := by
  have l1 := Proof.tautology (@neg_intro N φ ψ)
  sorry

def Γ_neg_elim {φ : Form N} {φ : Form N} (h : Γ ⊢ (∼∼φ)) : Γ ⊢ φ := by
  have l1 := Proof.tautology (@dne N φ)
  sorry

def Γ_conj_intro {φ : Form N} (h1 : Γ ⊢ φ) (h2 : Γ ⊢ ψ) : Γ ⊢ (φ ⋀ ψ) := by
  have l1 := Proof.tautology (@conj_intro N φ ψ)
  sorry

def Γ_conj_elim_l {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ φ := by
  have l1 := Proof.tautology (@conj_elim_l N φ ψ)
  sorry

def Γ_conj_elim_r {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ ψ := by
  have l1 := Proof.tautology (@conj_elim_r N φ ψ)
  sorry

def Γ_disj_intro_l {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (φ ⋁ ψ) := by
  have l1 := Proof.tautology (@disj_intro_l N φ ψ)
  sorry

def Γ_disj_intro_r {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (ψ ⋁ φ) := by
  have l1 := Proof.tautology (@disj_intro_r N φ ψ)
  sorry

def Γ_disj_elim {φ : Form N} (h1 : Γ ⊢ (φ ⋁ ψ)) (h2 : Γ ⊢ (φ ⟶ χ)) (h3 : Γ ⊢ (ψ ⟶ χ)) : Γ ⊢ χ := by
  have l1 := Proof.tautology (@disj_elim N φ ψ χ)
  sorry

lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
  sorry

def Γ_univ_intro {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) (h2 : occurs y φ = false) (h3 : is_substable φ y x) : Γ ⊢ φ → Γ ⊢ (all y, φ[y // x]) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := Proof.general x l1
      sorry

def Γ_univ_intro' {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) : Γ ⊢ φ → Γ ⊢ (all x, φ) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := Proof.general x l1
      sorry

def dn_equiv_premise {φ : Form N} : Γ ⊢ (∼∼φ) iff Γ ⊢ φ := by
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

def ax_nom_instance {φ : Form N} (i : NOM N) (m n : ℕ) : ⊢ (iterate_pos m (i ⋀ φ) ⟶ iterate_nec n (i ⟶ φ)) := by
  let x := φ.new_var
  have x_geq : x ≥ φ.new_var := by simp [SVAR.le]
  have l1 := @Proof.ax_nom N (φ[x//i]) x m n
  have l2 := Proof.ax_q2_nom (iterate_pos m (x⋀(φ[x//i]))⟶iterate_nec n (x⟶(φ[x//i]))) x i
  have l3 := Proof.mp l2 l1
  clear l1 l2
  rw [subst_nom, pos_subst, nec_subst, nom_svar_rereplacement x_geq] at l3
  exact l3

def rename_var (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ φ iff ⊢ (φ[y // x]) := by
  apply TypeIff.intro
  . intro h
    apply Proof.mp
    apply ax_q2_svar_instance
    exact y
    apply Proof.mp
    . apply Proof.mp
      apply Proof.tautology
      apply iff_elim_l
      apply rename_bound
      repeat assumption
    . apply Proof.general
      assumption
  . intro h
    apply Proof.mp
    apply ax_q2_svar_instance
    exact x
    apply Proof.mp
    . apply Proof.mp
      apply Proof.tautology
      apply iff_elim_r
      apply rename_bound
      repeat assumption
    . apply Proof.general
      assumption

def ax_q2_contrap {i : NOM N} {x : SVAR} : ⊢ (φ[i//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply Proof.tautology
    apply dni
  . apply Proof.mp
    apply Proof.tautology
    apply contrapositive
    apply Proof.ax_q2_nom

def ax_q2_svar_contrap {x y : SVAR} (h : is_substable φ y x) : ⊢ (φ[y//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply Proof.tautology
    apply dni
  . apply Proof.mp
    apply Proof.tautology
    apply contrapositive
    apply Proof.ax_q2_svar
    simp [is_substable]
    exact h

def ax_nom_instance' (x : SVAR) (m n : ℕ) : ⊢ (iterate_pos m (x ⋀ φ) ⟶ iterate_nec n (x ⟶ φ)) := by
  apply Proof.mp
  apply ax_q2_svar_instance
  assumption
  apply Proof.ax_nom

def dn_nec : ⊢ (□ φ ⟷ □ ∼∼φ) := by
  rw [Form.iff]
  apply Proof.mp
  apply Proof.mp
  apply Proof.tautology
  apply conj_intro
  repeat (
    apply Proof.mp
    apply Proof.ax_k
    apply Proof.necess
    apply Proof.tautology
    first | apply dni | apply dne
  )

def dn_all : ⊢ ((all x, φ) ⟷ all x, ∼∼φ) := by
  rw [Form.iff]
  apply Proof.mp
  apply Proof.mp
  apply Proof.tautology
  apply conj_intro
  sorry
  sorry

def bind_dual : ⊢((all x, ψ)⟷∼(ex x, ∼ψ)) := by
    rw [Form.bind_dual]
    apply Proof.mp; apply Proof.mp
    apply Proof.tautology
    apply iff_intro
    . apply hs
      . apply Proof.mp
        apply Proof.tautology
        apply iff_elim_l
        apply dn_all
      . apply Proof.tautology
        apply dni
    . apply hs
      . apply Proof.tautology
        apply dne
      . apply Proof.mp
        apply Proof.tautology
        apply iff_elim_r
        apply dn_all

def nec_dual : ⊢((□ ψ)⟷∼(◇ ∼ψ)) := by
    rw [Form.diamond]
    apply Proof.mp; apply Proof.mp
    apply Proof.tautology
    apply iff_intro
    . apply hs
      . apply Proof.mp
        apply Proof.tautology
        apply iff_elim_l
        apply dn_nec
      . apply Proof.tautology
        apply dni
    . apply hs
      . apply Proof.tautology
        apply dne
      . apply Proof.mp
        apply Proof.tautology
        apply iff_elim_r
        apply dn_nec

def diw_impl (h : ⊢(φ ⟶ ψ)) : ⊢ (◇φ ⟶ ◇ψ) := by
  have l1 := Proof.mp (Proof.tautology contrapositive) h
  have l2 := Proof.necess l1
  have l3 := Proof.mp Proof.ax_k l2
  have l4 := Proof.mp (Proof.tautology contrapositive) l3
  exact l4

def ax_brcn_contrap {φ : Form N} : ⊢ ((◇ ex x, φ) ⟶ (ex x, ◇ φ)) := by
  simp only [Form.diamond, Form.bind_dual]
  apply Proof.mp
  . apply Proof.tautology
    apply contrapositive
  . sorry

def iff_subst : ⊢ ((φ ⟷ ψ) ⟶ (ψ ⟷ χ) ⟶ (φ ⟷ χ)) := by
  apply Proof.tautology
  sorry

def pf_iff_subst : ⊢ (φ ⟷ ψ) → ⊢ (ψ ⟷ χ) → ⊢ (φ ⟷ χ) := by
  intro h1 h2
  apply Proof.mp
  apply Proof.mp
  apply iff_subst
  exact ψ
  repeat assumption
