import Hybrid.Lindenbaum
import Hybrid.ProofUtils

open Proof

def conjunction' (L : List (Form N)) : Form N :=
  match L with
    | []     => ⊥ ⟶ ⊥
    | [h]    => h
    | h :: t => h ⋀ conjunction' t

def has_wit_conj (Γ : Set (Form N)) : Form N → Form N → Prop
  | (ex x, ψ), φ => ∃ i : NOM N, ◇(((ex x, ψ) ⟶ ψ[i//x]) ⋀ φ) ∈ Γ
  | _, _         => True

def rename_bound_ex (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((ex x, φ) ⟷ ex y, φ[y // x]) := by
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

def l313 {τ χ : Form N} (h1 : is_substable χ y x) (h2 : occurs y τ = false) (h3 : occurs y χ = false) :
  ⊢ (◇ τ ⟶ ex y, ◇(((ex x, χ) ⟶ χ[y//x]) ⋀ τ)) := by
  have l1 := Γ_empty.mpr (rename_bound_ex h3 h1)
  sorry

theorem Form.new_var_properties (φ : Form N) : ∃ x : SVAR, x ≥ φ.new_var ∧ occurs x φ = false ∧ (∀ y : SVAR, is_substable φ x y) := by
  exists φ.new_var
  simp [SVAR.le, new_var_is_new]
  intro
  apply new_var_subst''
  simp [SVAR.le]

lemma l313' {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : ∀ ψ : Form N, has_wit_conj Δ ψ φ := by
  intro ψ
  unfold has_wit_conj
  split
  . next _ _ x ψ =>
      have ⟨y, geq, nocc, subst⟩ := (φ ⟶ ψ ⟶ all x, ⊥).new_var_properties
      have y_ne_x : y ≠ x := by
        intro habs
        have := habs ▸ (new_var_geq2 (new_var_geq1 (new_var_geq1 geq).2).2).1
        simp [SVAR.le, SVAR.add] at this
      have subst := subst x
      simp [occurs, is_substable, is_free] at nocc subst
      sorry
  . trivial

-- ◇ (((ex x, ψ)⟶ψ[y//x])⋀φ)
-- ◇ ((ex x, ψ⟶ψ[i//x])⋀φ)

def witness_conditionals (enum : ℕ → Form N) (n : ℕ) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : ∃ (l : List (Form N)), l ≠ [] ∧ ◇conjunction' l ∈ Δ :=
  match n with
  | 0   => by exists [φ]; sorry
  | n+1 => by
           let ⟨prev_l, prev_nnil, prev_mem⟩ := witness_conditionals enum n mcs wit mem
           let ψ_n := enum n
           have := l313' mcs wit prev_mem ψ_n
           match ψ_n with
           | ex x, ψ_n  =>
              let ⟨i_n, curr_mem⟩ := this
              exact ⟨((ex x, ψ_n) ⟶ ψ_n[i_n//x]) :: prev_l, by simp, by rw [conjunction']; exact curr_mem; exact prev_nnil⟩
           | _        => exact ⟨prev_l, prev_nnil, prev_mem⟩

def succesor_set' (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : Set (Form N) :=
  {ψ | □ψ ∈ Δ} ∪ {φ | ∃ n : ℕ, φ ∈ (witness_conditionals enum n mcs wit mem).choose}



/-
def Set.has_wit_of (Γ : Set (Form N)) : Form → Prop
  | ex x, φ => ∃ (i : NOM), (ex x, φ ⟶ φ[i//x]) ∈ Γ
  | _       => True

def Set.list_wit {Γ : Set (Form N)} (enum : ℕ → Form N) (n : ℕ) (h : ∀ i : ℕ, i < n → Γ.has_wit_of (enum i)) : List (Form N) :=
  match n with
  | 0   =>    []
  | n+1 =>    sorry

theorem set_family (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : Δ.MCS) (wit : Δ.witnessed) (mem : ◇φ ∈ Δ) :
  (n : ℕ) → (∃ Γ : Set (Form N), Canonical.R Δ Γ ∧ φ ∈ Γ ∧ ∀ i : ℕ, i < n → Γ.has_wit_of (enum i))
  | 0     => by
      let Γ₀ := {φ} ∪ {ψ | □ψ ∈ Δ}
      have : Γ₀.consistent := by sorry
      have ⟨Γ₀', incl, l_mcs⟩ := RegularLindenbaumLemma Γ₀ this
      exists Γ₀'
      apply And.intro
      . simp only [Canonical, restrict_by, mcs, l_mcs, true_and]
        intro φ mem
        apply incl; apply Or.inr; simp
        exact mem
      . simp; apply incl; simp
  | n+1   => by
      have ⟨Γ_ih, ⟨R_ih, ⟨mem_ih, wit_ih⟩⟩⟩ := set_family enum mcs wit mem n
      sorry

def succesor_set (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : Δ.MCS) (wit : Δ.witnessed) (mem : ◇φ ∈ Δ) : Set (Form N) :=
  {φ | ∃ n : ℕ, φ ∈ (set_family enum mcs wit mem n).choose}
-/
