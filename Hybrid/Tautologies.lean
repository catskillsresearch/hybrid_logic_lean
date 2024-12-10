import Hybrid.Model
import Hybrid.Tautology
open Classical

noncomputable def model_val_func (M : Model N) (s : M.W) (g : I M.W) : Form N → Bool :=
  λ φ => ite ((M,s,g) ⊨ φ) true false

noncomputable def model_eval (M : Model N) (s : M.W) (g : I M.W) : Eval N :=
    sorry

theorem taut_sound : Tautology φ → ⊨ φ := by
  intro h M s g
  have := h (model_eval M s g)
  sorry
