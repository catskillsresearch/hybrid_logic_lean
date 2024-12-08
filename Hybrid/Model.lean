import Hybrid.Substitutions

set_option linter.docPrime false

structure Model (N : Set ℕ) where
  W : Type
  R : W → W → Prop
  Vₚ: PROP → Set W
  Vₙ: NOM N  → W

-- interpretation function
-- from any state variable, to exactly ONE world
def I (W : Type) := SVAR → W

-- let's define what it means to have a path between two elements
-- under a relation R
-- we will need this in proofs
def path {α : Type} (R : α → α → Prop) (a b : α) (n : Nat) : Prop :=
  match n with
  | Nat.zero   => a = b
  | Nat.succ m => ∃ i : α, (R i b) ∧ (path R a i m)

@[simp]
def is_variant (g₁ g₂ : I W) (x : SVAR) := ∀ y : SVAR, ((x ≠ y) → (g₁ y = g₂ y))

@[simp]
def Sat (M : Model N) (s : M.W) (g : I M.W) : (φ : Form N) → Prop
  | Form.bttm     => False
  | Form.prop p   => s ∈ (M.Vₚ p)
  | Form.nom  i   => s = (M.Vₙ i)
  | Form.svar x   => s = (g x)
  | Form.impl ψ χ => (Sat M s g ψ) → (Sat M s g χ)
  | Form.box  ψ   => ∀ s' : M.W, (M.R s s' → (Sat M s' g ψ))
  | Form.bind x ψ => ∀ g' : I M.W, ((is_variant g' g x) → Sat M s g' ψ)

notation "(" M "," s "," g ")" "⊨" φ => Sat M s g φ
notation "(" M "," s "," g ")" "⊭" φ => ¬ Sat M s g φ

theorem neg_sat : ((M,s,g) ⊨ ∼φ) ↔ ((M,s,g) ⊭ φ) := by
  simp only [Sat, or_false]
theorem and_sat : ((M,s,g) ⊨ φ ⋀ ψ) ↔ (((M,s,g) ⊨ φ) ∧ (M,s,g) ⊨ ψ) := by
  simp
theorem or_sat  : ((M,s,g) ⊨ φ ⋁ ψ) ↔ (((M,s,g) ⊨ φ) ∨ (M,s,g) ⊨ ψ) := by
  simp
theorem pos_sat : (((M,s,g) ⊨ ◇φ) ↔ (∃ s' : M.W, (M.R s s' ∧ (M,s',g) ⊨ φ))) := by
  simp
theorem ex_sat  : ((M,s,g) ⊨ ex x, φ) ↔ (∃ g' : I M.W, (is_variant g' g x) ∧ ((M,s,g') ⊨ φ)) := by
  simp [-is_variant]
theorem iff_sat : ((M,s,g) ⊨ (φ ⟷ ψ)) ↔ (((M,s,g) ⊨ φ) ↔ (M,s,g) ⊨ ψ) := by
  rw [Form.iff, and_sat, Sat, Sat]
  apply Iff.intro
  . intro ⟨h1, h2⟩
    apply Iff.intro <;> assumption
  . intro h1
    apply And.intro <;> simp [h1]

@[simp]
def Valid (φ : Form N) := ∀ (M : Model N) (s : M.W) (g : I M.W), ((M, s, g) ⊨ φ)

prefix:1000 "⊨" => Valid
prefix:1000 "⊭" => ¬ Valid

@[simp]
def Sat_Set (M : Model N) (s : M.W) (g : I M.W) (Γ : Set (Form N)) := ∀ (φ : Form N), (φ ∈ Γ) → ((M, s, g) ⊨ φ)

notation "(" M "," s "," g ")" "⊨" Γ => Sat_Set M s g Γ
notation "(" M "," s "," g ")" "⊭" Γ => ¬ Sat_Set M s g Γ

--def Entails (Γ : set Form) (φ : Form) := ∀ M : Model, (M ⊨ Γ) → (M ⊨ φ)
@[simp]
def Entails (Γ : Set (Form N)) (φ : Form N) := ∀ (M : Model N) (s : M.W) (g : I M.W), ((M,s,g) ⊨ Γ) → ((M,s,g) ⊨ φ)


infix:1000 "⊨" => Entails
notation Γ "⊭" φ => ¬ (Entails Γ φ)

@[simp]
def satisfiable (Γ : Set (Form N)) := ∃ (M : Model N) (s : M.W) (g : I M.W), (M,s,g) ⊨ Γ
