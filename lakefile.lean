import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

package Hybrid {
  -- add package configuration options here
}

@[default_target]
lean_lib Hybrid {
  -- Explicitly list all your .lean files here
  roots := #[
    `Hybrid.PROP, `Hybrid.TotalSet, `Hybrid.SVAR, `Hybrid.TypeIff,
    `Hybrid.Completeness, `Hybrid.Eval, `Hybrid.Model, `Hybrid.Tautology,
    `Hybrid.Substitutions, `Hybrid.IteratedModalities, `Hybrid.Variables,
    `Hybrid.New_NOM, `Hybrid.NominalSubstitution, `Hybrid.FormSubstitution,
    `Hybrid.Nominals, `Hybrid.NOM, `Hybrid.Form, `Hybrid.Util, `Hybrid.Proof,
    `Hybrid.Tautologies, `Hybrid.Variants, `Hybrid.Satisfaction, `Hybrid.Truth,
    `Hybrid.Lemmas, `Hybrid.Soundness, `Hybrid.ExistenceLemma, `Hybrid.ListUtils,
    `Hybrid.RenameBound, `Hybrid.GeneralModel, `Hybrid.Canonical,
    `Hybrid.GeneratedSubmodel, `Hybrid.WitnessedModel, `Hybrid.ProofUtils,
    `Hybrid.FormCountable, `Hybrid.MCS, `Hybrid.CompletedModel,
    `Hybrid.StandardCompletedModel, `Hybrid.Lindenbaum, `Hybrid.LanguageExtension
  ]
}


