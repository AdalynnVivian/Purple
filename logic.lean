prelude

import .types

universes u v

notation `⊥` :=  ∀p: Prop, p

def not (p: Prop) := p → ⊥

instance lnot_Prop: has_lnot Prop Prop :=
  ⟨not⟩
axiom double_neg {p: Prop}: ¬¬p → p

structure and (p q: Prop) : Prop :=
  intro :: (left: p) (right: q)
instance Prop_wedge_Prop: has_wedge Prop Prop Prop :=
  ⟨and⟩

inductive or (p q: Prop) : Prop
  | inl (h: p) : or
  | inr (h: q) : or
instance Prop_vee_Prop: has_vee Prop Prop Prop :=
  ⟨or⟩

structure iff (p q: Prop) : Prop :=
  intro :: (mp: p → q) (mpr: q → p)
instance Prop_leftrightarrow_Pro: has_leftrightarrow Prop Prop Prop := ⟨iff⟩

def equ {α: Sort u} (a b: α) : Prop := ∀ϕ: α → Prop, ϕ a ↔ ϕ b
instance homo_eq(α: Sort u): has_eq α α Prop := ⟨equ⟩
def neq {α: Sort u} (a b: α) := ¬(a = b)

inductive Exists {α: Sort u} (ϕ: α → Prop) : Prop
  | intro (a: α) (h: ϕ a) : Exists
notation `∃` binders `, ` r:(scoped P, Exists P) := r

def exists_unique {α: Sort u} (ϕ: α → Prop) :=
  ∃ x, ϕ x ∧ ∀ y, ϕ y → y = x
notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r