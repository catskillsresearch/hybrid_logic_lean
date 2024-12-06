structure PROP where
  letter : Nat
deriving DecidableEq, Repr

instance : Max PROP where
  max := λ p => λ q => ite (p.letter > q.letter) p q
