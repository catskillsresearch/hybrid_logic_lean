import Hybrid.GeneratedSubmodel

def WitnessedModel {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralModel TotalSet := Θ.GeneratedSubmodel witnessed

def WitnessedI {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralI (Set (Form TotalSet)) := Θ.GeneratedSubI witnessed
