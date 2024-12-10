import Hybrid.Satisfaction

theorem D_help {Γ : Set (Form N)} : ((M,s,g)⊨Γ ∪ {φ}) ↔ (((M,s,g)⊨Γ) ∧ (M,s,g) ⊨ {φ}) := by
  apply Iff.intro
  . intro h
    rw [Sat_Set] at h
    apply And.intro
    . intro χ mem; apply h; simp [mem]
    . intro χ mem; apply h; simp at mem; simp [mem]
  . intro ⟨hl, hr⟩
    intro χ mem; simp at mem
    apply Or.elim mem <;> {
      intros; first | {apply hl; assumption} | {apply hr; assumption}
    }

theorem SemanticDeduction {Γ : Set (Form N)} : (Γ ⊨ (φ ⟶ ψ)) ↔ ((Γ ∪ {φ}) ⊨ ψ) := by
  apply Iff.intro <;> {
    intro h M s g sat_set
    try (intro sat_φ;
          have sat_φ : (M,s,g) ⊨ {φ} := by simp only [Sat_Set, Set.mem_singleton_iff, forall_eq,
            sat_φ])
    try (have := h M s g (D_help.mpr ⟨sat_set, sat_φ⟩))
    try (have ⟨sat_l, sat_r⟩ := D_help.mp sat_set;
          simp only [Sat_Set, Set.mem_singleton_iff, forall_eq] at sat_r ;
          have := (h M s g sat_l) sat_r)
    assumption
  }

def Model.odd_noms (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  Vₚ:= M.Vₚ
  Vₙ:= λ i => M.Vₙ ((i-1)/2)

def Model.odd_noms_inv (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  Vₚ:= M.Vₚ
  Vₙ:= λ i => M.Vₙ (i*2+1)

theorem sat_odd_noms {φ : Form TotalSet} : ((M,s,g) ⊨ φ) ↔ ((M.odd_noms,s,g) ⊨ φ.odd_noms) := by
  induction φ generalizing s g with
  | nom i =>
      simp [odd_nom, Model.odd_noms]
  | impl φ ψ ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box φ ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [←@ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x φ ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [←@ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Model.odd_noms]

theorem sat_odd_noms' {φ : Form TotalSet} : ((M,s,g) ⊨ φ.odd_noms) ↔ ((M.odd_noms_inv,s,g) ⊨ φ) := by
  induction φ generalizing s g with
  | nom i =>
      simp [odd_nom, Model.odd_noms, Model.odd_noms_inv]
  | impl φ ψ ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box φ ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [←@ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x φ ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [←@ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Model.odd_noms, Model.odd_noms_inv]
