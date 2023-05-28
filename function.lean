prelude

import .operations
import .core
import .logic
import .coe
universes u₁ u₂ u₃ u₄ u₅
variables {α: Sort u₁} {β: Sort u₂} {γ: Sort u₃} {δ: Sort u₄} {ε: Sort u₅}

@[inline, reducible] def comp (f: β → γ) (g: α → β): α → γ :=
  λx, f (g x)
instance fun_comp_fun(α: Sort u₁)(β: Sort u₂)(γ: Sort u₃): has_comp (β → γ) (α → β) (α → γ) :=
  has_comp.mk comp
@[inline, reducible] def dcomp {β: α → Sort u₂} {φ: Π{x: α}, β x → Sort u₃}
  (f: Π{x: α}(y: β x), φ y) (g: Πx, β x): Πx, φ (g x) :=
    λx, f (g x)
infix ` ∘' `:80 := dcomp

@[reducible] def comp_right (f: β → β → β) (g: α → β): β → α → β :=
  λb, λa, f b (g a)
@[reducible] def comp_left (f: β → β → β) (g: α → β): α → β → β :=
  λa, λb, f (g a) b
@[reducible] def on_fun (f: β → β → γ) (g: α → β): α → α → γ :=
  λx, λy, f (g x) (g y)
@[reducible] def combine (f: α → β → γ) (op: γ → δ → ε) (g: α → β → δ) : α → β → ε :=
  λx, λy, op (f x y) (g x y)
@[reducible] def const (β: Sort u₂) (a: α): β → α :=
  λx, a
@[reducible] def swap {γ: α → β → Sort u₃} (f: Πx, Πy, γ x y): Πy, Πx, γ x y :=
  λy, λx, f x y
@[reducible] def app {β: α → Sort u₂} (f: Πx, β x) (x: α): β x :=
  f x

lemma left_id (f: α → β): (@id β) ∘ f = f := eq.refl f 
lemma right_id (f: α → β): f ∘ (@id α) = f := eq.refl f
constant f: β → γ
constant g: α → β

#check f ∘ g 