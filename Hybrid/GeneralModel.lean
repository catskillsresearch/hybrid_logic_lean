import Hybrid.RenameBound

open Classical

def restrict_by : (Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) :=
  λ restriction => λ R => λ Γ => λ Δ => restriction Γ ∧ restriction Δ ∧ R Γ Δ

theorem path_conj {R : α → Prop} : path (λ a b => R a ∧ R b) a b n → (R a → R b) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2

theorem path_restr : path (restrict_by R₁ R₂) Γ Δ n → path R₂ Γ Δ n := by
  induction n generalizing Δ with
  | zero => simp only [path, imp_self]
  | succ n ih =>
      simp only [path]
      intro ⟨Θ, ⟨⟨_, _, h1⟩, h2⟩⟩
      exists Θ
      apply And.intro
      assumption
      apply ih
      assumption

theorem path_restr' : path (restrict_by R₁ R₂) Γ Δ n → (R₁ Γ → R₁ Δ) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2.1

structure GeneralModel (N : Set ℕ) where
  W : Type
  R : W → W  → Prop
  Vₚ: PROP   → Set W
  Vₙ: NOM N  → Set W

def GeneralI (W : Type) := SVAR → Set W
