structure SVAR where
  letter : Nat
deriving DecidableEq, Repr

instance svarmax : Max SVAR where
  max := λ x => λ y => ite (x.letter > y.letter) x y

instance : Coe SVAR Nat  := ⟨SVAR.letter⟩

instance : Coe Nat SVAR  := ⟨SVAR.mk⟩

instance SVAR.le : LE SVAR         where
  le    := λ x => λ y =>  x.letter ≤ y.letter

instance SVAR.lt : LT SVAR         where
  lt    := λ x => λ y =>  x.letter < y.letter

instance SVAR.add : HAdd SVAR Nat SVAR where
  hAdd  := λ x => λ n => (x.letter + n)
