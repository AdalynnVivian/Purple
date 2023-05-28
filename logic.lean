prelude

import .operations
import .core

noncomputable theory

universes u v w

lemma opt_param_eq (α: Sort u) (default: α): opt_param α default = α :=
  eq.refl α --should be @[simp]

@[inline] def id {α: Sort u} (a: α): α := a

def flip {α: Sort u} {β: Sort v} {γ: Sort w} (f: α → β → γ): β → α → γ :=
  λx, λy, f y x

/-! implication -/
def implies (p q: 𝔹): 𝔹 := p → q

lemma implies.trans {p q r: 𝔹} (h₁: p → q) (h₂: q → r): p → r :=
  λhp: p, h₂ (h₁ hp)
lemma trivial: true := true.intro

@[inline] def absurd {p: 𝔹} {a: Sort v} (h₁: p) (h₂: ¬p): a :=
  false.rec a (h₂ h₁)

lemma not.intro {p: 𝔹} (h: p → ⊥): ¬p :=
  h

lemma mt {p q: 𝔹} (h₁: p → q) (h₂: ¬q): ¬p :=
  λhp: p, h₂ (h₁ hp)

/-! not -/
lemma not_false: ¬⊥ := id
lemma non_contradictory_intro {p: 𝔹} (hp: p): ¬¬p :=
  λhnp: ¬p, hnp hp

/-! false -/
@[inline] def false.elim {C: Sort u} (h: ⊥): C :=
  false.rec C h

/-! eq -/
lemma proof_irrel {p: 𝔹} (h₁ h₂: p): h₁ = h₂ := eq.refl h₁
@[simp] def id.def {α: Sort u} (a: α): id a = a :=rfl
@[inline] def eq.mp {α β: Sort u}: (α = β) → α → β :=
  eq.rec_on
@[inline] def eq.mpr {α β: Sort u}: (α = β) → β → α :=
  λh, eq.mp (eq.symm h)
@[elab_as_eliminator] lemma eq.substr {α: Sort u} {ϕ: α → 𝔹} {a b: α} (h₁: b = a): ϕ a → ϕ b :=
  eq.subst (eq.symm h₁)
lemma congr {α: Sort u} {β: Sort v} {f₁ f₂: α → β} {a₁ a₂: α} (h₁: f₁ = f₂) (h₂: a₁ = a₂): f₁ a₁ = f₂ a₂ :=
  h₁ ▸ h₂ ▸ rfl
lemma congr_fun {α: Sort u} {β: α → Sort v} {f g: Π x, β x} (h: f = g) (a: α): f a = g a :=
  h ▸ eq.refl (f a)
lemma congr_arg {α: Sort u} {β: Sort v} {a₁ a₂: α} (f: α → β): a₁ = a₂ → f a₁ = f a₂ :=
  congr rfl
lemma trans_rel_left {α: Sort u} {x y z: α} (R: α → α → 𝔹) (h₁: R x y) (h₂: y = z): R x z :=
  h₂ ▸ h₁
lemma trans_rel_right {α: Sort u} {x y z: α} (R: α → α → 𝔹) (h₁: R x y) (h₂: x = z): R z y :=
  h₂ ▸ h₁
lemma of_eq_true {p: 𝔹} (h: p = ⊤): p :=
  h.symm ▸ trivial
lemma not_of_eq_false {p: 𝔹} (h: p = ⊥): ¬p :=
  λhp, h ▸ hp
@[inline] def cast {α β: Sort u} (h: α = β) (a: α): β :=
  eq.rec a h
lemma cast_proof_irrel {α β: Sort u} (h₁ h₂: α = β) (a: α): cast h₁ a = cast h₂ a :=
  eq.refl $ cast h₁ a
lemma cast_eq {α: Sort u} (h: α = α) (a: α): cast h a = a :=
  eq.refl a

/-! ne -/

instance ne_of_eq(α: Sort u)(β: Sort v)[has_eq α β 𝔹]: has_ne α β 𝔹 := 
  has_ne.mk (λx, λy, ¬(x = y))

@[reducible] def ne {α: Sort u} (a b: α) := ¬(a = b)
lemma ne.def {α: Sort u} (a b: α) : a ≠ b = ¬(a = b) := eq.refl (a ≠ b)

namespace ne
  variable {α: Sort u}
  variables {a b: α}
  lemma intro (h: a = b → ⊥): a ≠ b := h
  lemma elim (h: a ≠ b): a = b → ⊥ := h
  lemma irrefl (h: a ≠ a): ⊥ := h rfl
  lemma symm (h: a ≠ b): b ≠ a :=
    λh': b = a, h $ h'.symm
end ne

lemma false_of_ne {α: Sort u} {a: α}: a≠a → ⊥ :=
  ne.irrefl

section
  variable {p: Prop}

  lemma ne_false_of_self: p → p≠⊥ :=
    λhp: p, λheq: p = ⊥, heq ▸ hp
  lemma ne_true_of_not: ¬p → p≠⊤ :=
    λhnp: ¬p, λhpet: p=⊤, absurd (eq.mpr hpet trivial) hnp
  lemma true_ne_false: ⊤ ≠ ⊥ :=
    ne_false_of_self trivial
end