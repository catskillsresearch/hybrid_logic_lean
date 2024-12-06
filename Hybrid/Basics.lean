import Mathlib
import Hybrid.TotalSet
import Hybrid.PROP
import Hybrid.SVAR

open Classical

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

instance : IsTrans (NOM S) GT.gt where
  trans := λ _ _ _ h1 h2 => Nat.lt_trans h2 h1

instance : IsTotal (NOM S) GE.ge where
  total := λ a => λ b => Or.inl sorry
   -- simp [NOM.le, LE.le, Nat.le_total]

instance : IsTrans (NOM S) GE.ge where
  trans := λ _ _ _ h1 h2 => Nat.le_trans h2 h1

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

inductive Form (N : Set ℕ) where
  -- atomic formulas:
  | bttm : Form N
  | prop : PROP   → Form N
  | svar : SVAR   → Form N
  | nom  :  NOM N → Form N
  -- connectives:
  | impl : Form N → Form N → Form N
  -- modal:
  | box  : Form N → Form N
  -- hybrid:
  | bind :   SVAR → Form N → Form N
deriving DecidableEq, Repr

def Form.depth : Form N → ℕ
  | .impl φ ψ =>  1 + Form.depth φ + Form.depth ψ
  | .box  φ   =>  1 + Form.depth φ
  | .bind _ φ =>  2 + Form.depth φ
  | _       =>    0

instance : Nonempty (Form N) := ⟨Form.bttm⟩

@[simp]
def Form.neg      : Form N → Form N := λ φ => Form.impl φ Form.bttm
@[simp]
def Form.conj     : Form N → Form N → Form N := λ φ => λ ψ => Form.neg (Form.impl φ (Form.neg ψ))
@[simp]
def Form.iff      : Form N → Form N → Form N := λ φ => λ ψ => Form.conj (Form.impl φ ψ) (Form.impl ψ φ)
@[simp]
def Form.disj     : Form N → Form N → Form N := λ φ => λ ψ => Form.impl (Form.neg φ) ψ
@[simp]
def Form.diamond  : Form N → Form N := λ φ => Form.neg (Form.box (Form.neg φ))
@[simp,match_pattern]
def Form.bind_dual: SVAR → Form N → Form N := λ x => λ φ => Form.neg (Form.bind x (Form.neg φ))

instance : Coe PROP     (Form N)  := ⟨Form.prop⟩
instance : Coe SVAR     (Form N)  := ⟨Form.svar⟩
instance : Coe (NOM N)  (Form N)  := ⟨Form.nom⟩

infixr:60 "⟶" => Form.impl
infixl:65 "⋀" => Form.conj
infixl:65 "⋁" => Form.disj
prefix:100 "□" => Form.box
prefix:100 "◇ " => Form.diamond
notation:120 "all " x ", " φ => Form.bind x φ
notation:120 "ex " x ", " φ => Form.bind_dual x φ
prefix:170 "∼" => Form.neg
infixr:60 "⟷" => Form.iff
notation "⊥"  => Form.bttm

def conjunction (Γ : Set (Form N)) (L : List Γ) : Form N :=
match L with
  | []     => ⊥ ⟶ ⊥
  | h :: t => h.val ⋀ conjunction Γ t

def Form.new_var  : Form N → SVAR
| .svar x   => x+1
| .impl ψ χ => max (ψ.new_var) (χ.new_var)
| .box  ψ   => ψ.new_var
| .bind x ψ => max (x+1) (ψ.new_var)
| _         => ⟨0⟩


def Form.new_nom  : Form TotalSet → NOM TotalSet
| .nom  i   => i+1
| .impl ψ χ => max (ψ.new_nom) (χ.new_nom)
| .box  ψ   => ψ.new_nom
| .bind _ ψ => ψ.new_nom
| _         => ⟨0, trivial⟩
