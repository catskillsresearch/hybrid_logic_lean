import Hybrid.Model

noncomputable def model_val_func (M : Model N) (s : M.W) (g : I M.W) : Form N → Bool := λ φ => ite ((M,s,g) ⊨ φ) true false

noncomputable def model_eval (M : Model N) (s : M.W) (g : I M.W) : Eval N :=
    let f := model_val_func M s g
    have p1 : f ⊥ = false := by simp [model_val_func]
    have p2 : ∀ φ ψ : Form N, (f (φ ⟶ ψ) = true) ↔ (¬(f φ) = true ∨ (f ψ) = true) := λ φ ψ : Form N => by simp [model_val_func]
    ⟨f, p1, p2⟩

theorem taut_sound : Tautology φ → ⊨ φ := by
  intro h M s g
  have := h (model_eval M s g)
  simp [model_eval, model_val_func] at this
  exact this
