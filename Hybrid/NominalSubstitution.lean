import Hybrid.New_NOM

def nom_subst_nom : Form N → NOM N → NOM N → Form N
| .nom a, i, j     => if a = j then i else a
| .impl φ ψ, i, j  => nom_subst_nom φ i j ⟶ nom_subst_nom ψ i j
| .box φ, i, j     => □ nom_subst_nom φ i j
| .bind y φ, i, j  => all y, nom_subst_nom φ i j
| φ, _, _          => φ

def nom_subst_svar : Form N → SVAR → NOM N → Form N
| .nom a, i, j     => if a = j then i else a
| .impl φ ψ, i, j  => nom_subst_svar φ i j ⟶ nom_subst_svar ψ i j
| .box φ, i, j     => □ nom_subst_svar φ i j
| .bind y φ, i, j  => all y, nom_subst_svar φ i j
| φ, _, _          => φ

notation:150 φ "[" i "//" a "]" => nom_subst_nom φ i a
notation:150 φ "[" i "//" a "]" => nom_subst_svar φ i a

def all_nocc (i : NOM N) (Γ : Set (Form N)) := ∀ (φ : Form N), φ ∈ Γ → nom_occurs i φ = false

theorem all_noc_conj (h : all_nocc i Γ) (L : List Γ) : nom_occurs i (conjunction Γ L) = false := by
  induction L with
  | nil => simp [conjunction, nom_occurs]
  | cons head tail ih =>
      simp [conjunction, nom_occurs, ih, -Form.conj]
      exact h head head.2

def Form.bulk_subst : Form N → List (NOM N) → List (NOM N) → Form N
| φ, h₁ :: t₁, h₂ :: t₂ => bulk_subst (φ[h₁ // h₂]) t₁ t₂
| φ, _, []    =>  φ
| φ, [], _    =>  φ

def Form.list_noms : (Form N) → List (NOM N)
| nom  i   => [i]
| impl φ ψ => (List.merge sorry φ.list_noms sorry).dedup
| box φ    => φ.list_noms
| bind _ φ => φ.list_noms
| _        => []

def Form.odd_list_noms : Form TotalSet → List (NOM TotalSet) := λ φ => φ.list_noms.map (λ i => 2*i+1)

def Form.odd_noms : Form TotalSet → Form TotalSet := λ φ => φ.bulk_subst φ.odd_list_noms φ.list_noms

def Set.odd_noms : Set (Form TotalSet) → Set (Form TotalSet) := λ Γ => {Form.odd_noms φ | φ ∈ Γ}

def nocc_bulk_property (l1 l2 : List (NOM TotalSet)) (φ : Form TotalSet) := ∀ {n : Fin l1.length} {i : NOM TotalSet}, (i = l1[n]) → (i ∉ φ.list_noms ∨ i ∈ l2.take n) ∧ i ∉ l1.take n

theorem list_noms_sorted_ge {φ : Form N} : φ.list_noms.Sorted GE.ge := by
  induction φ with
  | nom  i   => simp [Form.list_noms]
  | impl φ ψ ih1 ih2 =>
      exact List.Pairwise.sublist ((List.merge sorry φ.list_noms sorry).dedup_sublist) sorry
  | box _ ih    => exact ih
  | bind _ _ ih => exact ih
  | _        => simp [Form.list_noms]

theorem list_noms_nodup {φ : Form N} : φ.list_noms.Nodup := by
  induction φ <;> simp [Form.list_noms, List.nodup_dedup, *]

theorem list_noms_sorted_gt {φ : Form N} : φ.list_noms.Sorted GT.gt := by
  simp [List.Sorted, List.Pairwise, GT.gt, NOM.gt_iff_ge_and_ne]
  sorry

theorem list_noms_chain' {φ : Form N} : φ.list_noms.Chain' GT.gt := by
  rw [List.chain'_iff_pairwise]
  exact list_noms_sorted_gt
