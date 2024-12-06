import Mathlib
import Hybrid.TotalSet

structure NOM (N : Set ℕ) where
  letter : N
deriving DecidableEq, Repr

instance : Max (NOM S) where
  max := λ i => λ j => ite (i.letter > j.letter) i j

theorem NOM_eq {i j : NOM S} : (i = j) ↔ (i.letter = j.letter) := by
  cases i
  cases j
  simp

theorem NOM_eq' {i j : NOM S} : (i = j) ↔ (j.letter = i.letter) := by
  cases i
  cases j
  simp
  apply Iff.intro <;> {intro; simp [*]}

instance : OfNat (NOM TotalSet) n     where
  ofNat := NOM.mk  ⟨n, trivial⟩

instance NOM.le : LE (NOM S)       where
  le    := λ x => λ y =>  x.letter ≤ y.letter

instance NOM.lt : LT (NOM S)         where
  lt    := λ x => λ y =>  x.letter < y.letter

instance : IsTrans (NOM S) GT.gt where
  trans := λ _ _ _ h1 h2 => Nat.lt_trans h2 h1

instance : IsTrans (NOM S) GE.ge where
  trans := λ _ _ _ h1 h2 => Nat.le_trans h2 h1

instance : IsTotal (NOM S) GE.ge where
  total := λ a => λ b =>
    match Nat.le_total a.letter b.letter with
    | Or.inl h => Or.inr h
    | Or.inr h => Or.inl h

theorem NOM.gt_iff_ge_and_ne {a b : (NOM S)} : a > b ↔ (a ≥ b ∧ a ≠ b) := by
  simp only [GT.gt, GE.ge, NOM.lt, NOM.le, LE.le, LT.lt, NOM.mk, ne_eq, NOM_eq']
  apply Iff.intro
  . intro h
    apply And.intro
    . exact (Nat.lt_iff_le_and_ne.mp h).1
    . have := (Nat.lt_iff_le_and_ne.mp h).2
      intro habs
      simp [habs] at this
  . rw [←ne_eq]
    intro ⟨h1, h2⟩
    apply Nat.lt_iff_le_and_ne.mpr
    apply And.intro
    . exact h1
    . intro habs
      apply h2
      apply Subtype.eq
      assumption

@[simp] instance NOM.add : HAdd (NOM TotalSet) Nat (NOM TotalSet) where
  hAdd  := λ x => λ n => ⟨(x.letter + n), trivial⟩

@[simp] instance : HSub (NOM TotalSet) Nat (NOM TotalSet) where
  hSub  := λ x => λ n => ⟨(x.letter - n), trivial⟩

@[simp] instance : HMul (NOM TotalSet) Nat (NOM TotalSet) where
  hMul  := λ x => λ n => ⟨(x.letter * n), trivial⟩

@[simp] instance : HDiv (NOM TotalSet) Nat (NOM TotalSet) where
  hDiv  := λ x => λ n => ⟨(x.letter / n), trivial⟩

@[simp] instance NOM.hmul : HMul Nat (NOM TotalSet) (NOM TotalSet) where
  hMul  := λ n => λ x => ⟨(x.letter * n), trivial⟩

@[simp] instance : HMul (NOM TotalSet) ℕ ℕ where
  hMul  := λ x => λ n => x.letter * n
