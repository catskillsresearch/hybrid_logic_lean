import Hybrid.Proof
import Hybrid.Substitutions
import Hybrid.Util

open Proof

def Form.total : Form N → Form TotalSet
  | .bttm     => Form.bttm
  | .prop p   => Form.prop p
  | .svar v   => Form.svar v
  | .nom i    => Form.nom ⟨i.1.1, trivial⟩
  | .impl ψ χ => Form.impl ψ.total χ.total
  | .box ψ    => Form.box ψ.total
  | .bind v ψ => Form.bind v ψ.total

theorem total_inj' {φ ψ : Form N} : φ.total = ψ.total → φ = ψ := by
  induction φ generalizing ψ with
  | impl a b ih1 ih2 =>
        cases ψ with
        | impl c d => simp [Form.total, -implication_disjunction]
                      intros
                      apply And.intro <;> (first | apply ih1 | apply ih2) <;> assumption
        | _    => simp [Form.total]
  | box a ih | bind v a ih =>
      cases ψ with
      | box b    => simp [Form.total, -implication_disjunction]; try apply ih
      | bind u b => simp [Form.total, -implication_disjunction];
                    try (intro; simp only [*, true_and]; apply ih)
      | _     => simp  [Form.total]
  | _    => cases ψ <;> simp [Form.total, NOM_eq, -implication_disjunction] <;>
                        (intros; apply Subtype.eq; assumption)

lemma total_inj {N : Set ℕ} : (@Form.total N).Injective := by
  unfold Function.Injective
  apply total_inj'

noncomputable def Form.inv_t : Form TotalSet → Form N := Function.invFun Form.total

lemma total_inv_is_inv : Function.LeftInverse (@Form.inv_t N) Form.total := by
  apply Function.leftInverse_invFun
  apply total_inj'

notation φ"⁺" => Form.total φ
notation φ"⁻" => Form.inv_t φ

theorem total_impl {φ : Form N} : φ⁺ = (ψ ⟶ χ) → φ = (ψ⁻ ⟶ χ⁻) := by
  intro h
  cases φ with
  | impl φ ψ =>
    simp [Form.total] at h ⊢
    apply And.intro
    . rw [←total_inv_is_inv φ]
      exact congr_arg (@Form.inv_t N) h.1
    . rw [←total_inv_is_inv ψ]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

theorem total_box {φ : Form N} : φ⁺ = □ ψ → φ = □ ψ⁻ := by
  intro h
  cases φ with
  | box φ =>
    simp [Form.total] at h ⊢
    rw [←total_inv_is_inv φ]
    exact congr_arg (@Form.inv_t N) h
  | _ => simp [Form.total] at *

theorem total_bind {φ : Form N} : φ⁺ = (all x, ψ) → φ = (all x, ψ⁻) := by
  intro h
  cases φ with
  | bind x φ =>
    simp [Form.total] at h ⊢
    apply And.intro
    . exact h.1
    . rw [←total_inv_is_inv φ]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

theorem total_subst_svar {φ : Form N} {x y : SVAR} : φ⁺ = ψ[y//x] → φ = ψ⁻[y//x] := by
  intro h
  sorry

theorem total_ax_k {φ : Form N} (h : φ⁺ = □(ψ ⟶ χ) ⟶ (□ψ ⟶ □χ)) : φ = □(ψ⁻ ⟶ χ⁻) ⟶ (□ψ⁻ ⟶ □χ⁻) := by
  cases φ with
  | impl φ_l φ_r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . have hyp := h.1
        clear h
        cases φ_l with
        | box φ_l_b =>
            simp [Form.total] at hyp ⊢
            cases φ_l_b with
            | impl φ_l_b_l φ_l_b_r =>
                apply total_impl
                assumption
            | _ =>  simp [Form.total] at *
        | _ => simp [Form.total] at *
      . have hyp := h.2
        clear h
        cases φ_r with
        | impl φ_r_l φ_r_r =>
            simp [Form.total] at hyp ⊢
            apply And.intro
            . apply total_box hyp.1
            . apply total_box hyp.2
        | _ => simp [Form.total] at hyp ⊢
  | _ => simp [Form.total] at *

theorem total_ax_q1 {φ : Form N} {x : SVAR} (h : φ⁺ = (all x, ψ ⟶ χ) ⟶ (ψ ⟶ all x, χ)) : φ = (all x, ψ⁻ ⟶ χ⁻) ⟶ (ψ⁻ ⟶ all x, χ⁻) := by
  cases φ with
  | impl l r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . have h := h.1
        cases l with
        | bind x l =>
            simp [Form.total] at h ⊢
            simp [h]
            apply total_impl h.2
        | _ => simp [Form.total] at *
      . have h := h.2
        cases r with
        | impl rl rr =>
            simp [Form.total] at h ⊢
            apply And.intro
            . rw [←total_inv_is_inv rl]
              exact congr_arg (@Form.inv_t N) h.1
            . apply total_bind h.2
        | _ => simp [Form.total] at h ⊢
  | _ => simp [Form.total] at *

theorem total_ax_q2_svar {φ : Form N} {x y : SVAR} (h : φ⁺ = (all x, ψ) ⟶ ψ[y // x]) : φ = (all x, ψ⁻) ⟶ ψ⁻[y//x] := by
  cases φ with
  | impl l r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . apply total_subst_svar h.2
      . apply total_bind h.1
  | _ => simp [Form.total] at h ⊢

lemma total_tautology {φ : Form N} : Tautology φ ↔ Tautology φ.total := by
  sorry

lemma total_subst_svar' {φ : Form N} {x y : SVAR} : (φ[y // x]).total = (φ.total)[y // x] := by
  sorry

lemma total_subst_nom {φ : Form N} {i : NOM N} {x : SVAR} : (φ[i // x]).total = (φ.total)[⟨i.1.1, trivial⟩ // x] := by
  sorry

lemma total_iterate_pos {φ : Form N} : (iterate_pos n φ).total = iterate_pos n (φ.total) := by
  sorry

lemma total_iterate_nec {φ : Form N} : (iterate_nec n φ).total = iterate_nec n (φ.total) := by
  sorry

def l416 {φ : Form N} {x : SVAR} (i : NOM N) : (pf : ⊢ φ) → (h : pf.fresh_var x) → ⊢ (φ[x // i]) :=
  sorry

def pf_extended {φ : Form N} : ⊢ φ iff ⊢ φ.total :=
  sorry
