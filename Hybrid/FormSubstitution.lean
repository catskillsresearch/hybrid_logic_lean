import Mathlib
import Hybrid.Util

def occurs (x : SVAR) (φ : Form N) : Bool :=
  match φ with
  | Form.bttm     => false
  | Form.prop _   => false
  | Form.svar y   => x = y
  | Form.nom  _   => false
  | Form.impl φ ψ => (occurs x φ) || (occurs x ψ)
  | Form.box  φ   => occurs x φ
  | Form.bind _ φ => occurs x φ

def is_free (x : SVAR) (φ : Form N) : Bool :=
  match φ with
  | Form.bttm     => false
  | Form.prop _   => false
  | Form.svar y   => x == y
  | Form.nom  _   => false
  | Form.impl φ ψ => (is_free x φ) || (is_free x ψ)
  | Form.box  φ   => is_free x φ
  | Form.bind y φ => (y != x) && (is_free x φ)

def is_bound (x : SVAR) (φ : Form N) := (occurs x φ) && !(is_free x φ)

-- conventions for substitutions can get confusing
-- "φ[s // x], the formula obtained by substituting s for all *free* occurrences of x in φ"
-- for reference: Blackburn 1998, pg. 628
def subst_svar (φ : Form N) (s : SVAR) (x : SVAR) : Form N :=
  match φ with
  | Form.bttm     => φ
  | Form.prop _   => φ
  | Form.svar y   => ite (x = y) s y
  | Form.nom  _   => φ
  | Form.impl φ ψ => (subst_svar φ s x) ⟶ (subst_svar ψ s x)
  | Form.box  φ   => □ (subst_svar φ s x)
  | Form.bind y φ => ite (x = y) (Form.bind y φ) (Form.bind y (subst_svar φ s x))

def subst_nom (φ : Form N) (s : NOM N) (x : SVAR) : Form N :=
  match φ with
  | Form.bttm     => φ
  | Form.prop _   => φ
  | Form.svar y   => ite (x = y) s y
  | Form.nom  _   => φ
  | Form.impl φ ψ => (subst_nom φ s x) ⟶ (subst_nom ψ s x)
  | Form.box  φ   => □ (subst_nom φ s x)
  | Form.bind y φ => ite (x = y) (Form.bind y φ) (Form.bind y (subst_nom φ s x))

def is_substable (φ : Form N) (y : SVAR) (x : SVAR) : Bool :=
  match φ with
  | Form.bttm     => true
  | Form.prop _   => true
  | Form.svar _   => true
  | Form.nom  _   => true
  | Form.impl φ ψ => (is_substable φ y x) && (is_substable ψ y x)
  | Form.box  φ   => is_substable φ y x
  | Form.bind z φ =>
      if (is_free x φ == false) then true
      else z != y && is_substable φ y x

notation:150 φ "[" s "//" x "]" => subst_svar φ s x
notation:150 φ "[" s "//" x "]" => subst_nom  φ s x
