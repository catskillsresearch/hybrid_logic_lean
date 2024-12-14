import Hybrid.Form
import Hybrid.Util

def pow2list (l : List (ℕ × ℕ × ℕ × ℕ)) := List.map (λ (a,b,c,d) => (2^(a+1), 2^(b+1), 2^(c+1), 2^(d+1))) l

def pow3list (l : List (ℕ × ℕ × ℕ × ℕ)) := List.map (λ (a,b,c,d) => (3^(a+1), 3^(b+1), 3^(c+1), 3^(d+1))) l

def squash (n m : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) := pow2list n ++ pow3list m

def Form.encode (N : Set ℕ) : Form N → List (ℕ × ℕ × ℕ × ℕ)
  | Form.bttm    => [(0,0,0,1)]
  | Form.prop p  => [(0,0,p.letter+1,0)]
  | Form.svar x  => [(0,x.letter+1,0,0)]
  | Form.nom i   => [(i.letter+1,0,0,0)]
  | Form.impl φ ψ   => [(0,0,0,2)] ++ (squash φ.encode ψ.encode)
  | Form.box φ   => [(0,0,0,3)] ++ φ.encode
  | Form.bind x φ=> [(0,0,0,4), (0,x.letter+1,0,0)] ++ φ.encode

-- Now to show that Form.encode is injective...

lemma l_bool_to_prop {tail1 tail2 : List (ℕ × ℕ × ℕ × ℕ)} (h: tail1 <+: tail2): tail1.isPrefixOf tail2 = true :=
  by exact List.isPrefixOf_iff_prefix.mpr h

lemma l_prop_to_bool {tail1 tail2 : List (ℕ × ℕ × ℕ × ℕ)} (h: tail1.isPrefixOf (tail2 ++ [t]) = true): tail1 <+: tail2 ++ [t] :=
  by exact List.isPrefixOf_iff_prefix.mp h

lemma is_prefix_append {a l : List (ℕ × ℕ × ℕ × ℕ)} (t : (ℕ × ℕ × ℕ × ℕ)) (hyp : l.isPrefixOf a) : l.isPrefixOf (a++[t]) := by
  induction l generalizing a with
  | nil => simp
  | cons head tail ih =>
      cases a with
      | nil =>
          simp at hyp
      | cons head2 tail2 =>
          simp [List.isPrefixOf] at hyp
          simp [List.isPrefixOf]
          have hl := hyp.left
          have hr := hyp.right
          have hr_bool := l_bool_to_prop hr
          have ih_app := @ih tail2 hr_bool
          have ih_bool := l_prop_to_bool ih_app
          exact ⟨hl, ih_bool⟩

theorem prefix_to_suffix {a l : List (ℕ × ℕ × ℕ × ℕ)} (h : l <:+ a) : l.reverse <+: a.reverse :=
  h.rec fun w h ↦ ⟨w.reverse, h.rec (List.reverse_append _ _).symm⟩

lemma is_suffix_cons {a l : List (ℕ × ℕ × ℕ × ℕ)} (h : ℕ × ℕ × ℕ × ℕ) (hyp : l.isSuffixOf a) : l.isSuffixOf (h::a) := by
  simp [List.isSuffixOf] at *
  have a' := List.reverse a
  have l' := List.reverse l
  have hyp' := prefix_to_suffix hyp
  have hyp'' := l_bool_to_prop hyp'
  have ipa := @is_prefix_append (List.reverse a) (List.reverse l) h
  have ipah := ipa hyp''
  have ipah' := l_prop_to_bool ipah
  exact ipah'

lemma sum_is_prefix {a b n m : List (ℕ × ℕ × ℕ × ℕ)} (h1 : a ++ b = n ++ m) (h2 : a.length ≤ n.length) : a <+: n := by
  induction a generalizing n with
  | nil =>  simp [List.IsPrefix]
  | cons ha ta iha =>
      cases n with
      | nil =>
          simp at h2
      | cons hn tn =>
          simp [List.IsPrefix]
          simp at h1
          apply And.intro
          . simp [h1.left]
          . simp at h2
            have h2' : ta.length.succ ≤ tn.length.succ := Nat.succ_le_succ h2
            have ih := iha h1.right (Nat.le_of_succ_le_succ h2')
            exact ih


lemma is_prefix_self {a : List (ℕ × ℕ × ℕ × ℕ)} : a.isPrefixOf a := by
  induction a with
  | nil =>
      simp
  | cons h t ih =>
      simp [List.isPrefixOf, ih]

lemma split_prefix_suffix {a b : List (ℕ × ℕ × ℕ × ℕ)} (hyp : a.isPrefixOf b) : ∃ c, c.isSuffixOf b ∧ b = a ++ c := by
  induction a generalizing b with
  | nil =>
      let c := b
      exists c
      simp [List.isSuffixOf, List.isPrefixOf, is_prefix_self]
  | cons ha ta ih =>
      cases b with
      | nil =>
          simp at hyp
      | cons hb tb =>
          simp [List.isPrefixOf] at hyp
          have ⟨h1, h2⟩ := hyp
          clear hyp
          sorry

theorem prime_2_3 (n m : Nat) : 3^(n+1) ≠ 2^(m+1) := by sorry

lemma pow2listinj : pow2list.Injective := by
  intro l1 l2 hyp
  induction l1 generalizing l2 with
  | nil =>
      cases l2 with
      | nil  => simp at *
      | cons => simp [pow2list] at hyp
  | cons h t ih =>
      cases l2 with
      | nil  => simp [pow2list] at hyp
      | cons head tail =>
          simp [pow2list] at hyp ⊢
          apply And.intro
          . have ⟨eq1, eq2, eq3, eq4⟩ := hyp.left
            clear ih hyp
            sorry
          . exact ih hyp.right

theorem pow3listinj : pow3list.Injective := by
  intro l1 l2 hyp
  induction l1 generalizing l2 with
  | nil =>
      cases l2 with
      | nil  => simp at *
      | cons => simp [pow3list] at hyp
  | cons h t ih =>
      cases l2 with
      | nil  => simp [pow3list] at hyp
      | cons head tail =>
          simp [pow3list] at hyp ⊢
          apply And.intro
          . have ⟨eq1, eq2, eq3, eq4⟩ := hyp.left
            clear ih hyp
            sorry
          . exact ih hyp.right

lemma guns : x ∈ pow2list a → ∃ n, x.fst = 2^(n+1) := by
  sorry

lemma of_brixton {a : List (ℕ × ℕ × ℕ × ℕ)} : (h :: t).isSuffixOf a → h ∈ a := by
  sorry

lemma suffix_pow2 {a : List (ℕ × ℕ × ℕ × ℕ)} : (h :: t).isSuffixOf (pow2list a) → ∃ n, h.fst = 2^(n+1) := by
  intro hyp
  exact guns (of_brixton hyp)

lemma squash_lemma_wlog (h : (pow2list a).length ≤ (pow2list n).length) : squash a b = squash n m → (pow2list a = pow2list n ∧ pow3list b = pow3list m) := by
  intro hyp
  simp [squash] at hyp
  have by_l1 := sum_is_prefix hyp h
  have by_l2 := split_prefix_suffix by_l1
  match by_l2 with
  | ⟨suf, hsuf⟩ =>
      clear h by_l1 by_l2
      simp [hsuf] at hyp
      cases suf
      . simp at hyp hsuf
        sorry
      . exfalso
        have is_pow_2 := suffix_pow2 hsuf.left
        cases b
        . simp [pow3list] at hyp
        . simp [pow3list, Prod.eq_iff_fst_eq_snd_eq] at hyp
          have abs_1 := hyp.left.left
          match is_pow_2 with
          | ⟨n, abs_2⟩ =>
              rw [abs_2] at abs_1
              apply prime_2_3
              apply abs_1

lemma squash_lemma : squash a b = squash n m → (pow2list a = pow2list n ∧ pow3list b = pow3list m) := by
  by_cases h : (pow2list a).length ≤ (pow2list n).length
  . exact squash_lemma_wlog h
  . simp at h
    have h := Nat.le_of_lt h
    conv =>
      congr
      . rw [eq_symm]
      . congr <;> rw [eq_symm]
    let Haux := @squash_lemma_wlog n a m b h
    exact squash_lemma_wlog h

theorem squash_inj : squash a b = squash n m → (a = n ∧ b = m) := by
  intro hyp
  have ⟨a_n, b_m⟩ := squash_lemma hyp
  exact ⟨pow2listinj a_n, pow3listinj b_m⟩

theorem Inject_Form (N : Set ℕ) : (Form.encode N).Injective := by
  intro φ ψ
  intro h
  induction φ generalizing ψ with
  | impl a b ih1 ih2  =>
      cases ψ <;> simp [Form.encode, -implication_disjunction] at *
      apply And.intro <;> (first | apply ih1 | apply ih2) <;> simp [squash_inj h]
  | box φ ih  =>
      cases ψ <;> first | simp [Form.encode, -implication_disjunction] at *; try apply ih; try assumption
  | bind x φ ih  =>
      cases ψ <;> simp [Form.encode, -implication_disjunction] at *
      apply And.intro
      . exact congrArg SVAR.mk h.left
      . exact ih h.right
  | _  =>
      induction ψ <;> simp [Form.encode] at * <;>
        first | exact congrArg PROP.mk h | exact congrArg SVAR.mk h |
        . simp [NOM_eq]
          apply Subtype.eq
          assumption

instance : Countable (Form N) := (Inject_Form N).countable
instance : Nonempty  (Form N) := ⟨⊥⟩
