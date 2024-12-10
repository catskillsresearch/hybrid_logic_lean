import Hybrid.Lemmas
import Hybrid.Tautologies
import Hybrid.Proof

theorem WeakSoundness : (⊢ φ) → (⊨ φ) := by
  intro pf
  induction pf with

  | tautology h => exact taut_sound h

  | ax_k =>
      intro M s g
      unfold Sat
      intro nec_impl nec_phi (s' : M.W) (rel : M.R s s')
      exact (nec_impl s' rel) (nec_phi  s' rel)

  | ax_q1 _ _ p =>
      intro M s g h1 h2 g' variant
      have := generalize_not_free p M s g
      rw [iff_sat] at this
      have := ((this.mp h2) g' variant)
      exact (h1 g' variant) this

  | ax_q2_svar _ x y h_subst =>
      intro M s g
      intro h
      -- let's build an explicit x-variant of g, named g'
      let g' : I M.W := λ v => ite (v ≠ x) (g v) (g y)
      have h_var : is_variant g g' x := by
        intro v x_not_v
        sorry
      have h_which_var : g' x = g y := sorry
      -- this exact g' can be used in the substitution lemma we proved
      rw [svar_substitution h_subst h_var h_which_var]
      -- now the goal becomes immediately provable
      exact h g' (is_variant_symm.mp h_var)

  | ax_q2_nom _ x i =>
      intro M s g
      intro h
      let g' : I M.W := λ v => ite (v ≠ x) (g v) (M.Vₙ i)
      have h_var : is_variant g g' x := by
        intro v x_not_v
        sorry
      have h_which_var : g' x = M.Vₙ i := sorry
      rw [nom_substitution h_var h_which_var]
      exact h g' (is_variant_symm.mp h_var)

  | ax_name v =>
      intro M s g
      rw [ex_sat]
      let g' : I M.W := λ x => ite (v = x) s (g x)
      apply Exists.intro
      . apply And.intro
        . exact show is_variant g' g v by
            rw [is_variant]
            intro y v_not_y
            sorry
        . sorry

  | ax_nom n m =>
      intro _ _ _ _ _ h
      rw [sat_iterated_pos] at h
      rw [sat_iterated_nec]
      intro s'' _ s''_sat_v
      match h with
      | ⟨s', _, s'_sat⟩ =>
          rw [and_sat] at s'_sat
          have s'_sat_v := s'_sat.left
          have s'_sat_φ := s'_sat.right
          have s''_is_s' := svar_unique_state s'_sat_v s'' s''_sat_v
          rw [s''_is_s']
          exact s'_sat_φ

  | @ax_brcn φ v =>
      intro M s g (h : (M,s,g) ⊨ all v, □φ) s' sRs' g' g_var_g'_v
      exact (h g' g_var_g'_v) s' sRs'

  | general _ _ ih =>
      intro M s _ g' _
      exact ih M s g'

  | @necess _ _ ih =>
      intro M _ g s' _
      exact ih M s' g

  | mp _ _ ih_maj ih_min =>
      intro M s g
      exact (ih_maj M s g) (ih_min M s g)

theorem Soundness : (Γ ⊢ φ) → (Γ ⊨ φ) := by
  rw [SyntacticConsequence]
  intro h
  apply SetEntailment
  match h with
  | ⟨L, conseq⟩ =>
    exists L
    apply WeakSoundness
    assumption

theorem Consistency : ∀ {N : Set ℕ}, ⊬ (@Form.bttm N) := by
  intro N habs
  have bot_valid := WeakSoundness habs
  let M : Model N := ⟨ℕ, λ _ => λ _ => True, λ _ => ∅,  λ _ => 0⟩
  have g : I (M.W) := λ _ => 0
  have := bot_valid M 0 g
  exact this

theorem npf_negpf : ⊢ (∼φ) → ⊬ φ := by
  intro h habs
  have := Proof.mp h habs
  exact Consistency this

theorem pos_npf_not : ⊢(◇φ) → ⊬(∼φ) := by
  rw [Form.diamond]
  intro h habs
  have := Proof.necess habs
  have := Proof.mp h this
  exact Consistency this
