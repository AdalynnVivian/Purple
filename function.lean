prelude

import .operations
import .core
import .logic
import .coe

noncomputable theory

set_option pp.beta true

namespace function
universes u₁ u₂ u₃ u₄ u₅
variables {α: Sort u₁} {β: Sort u₂} {γ: Sort u₃} {δ: Sort u₄} {ζ: Sort u₅} --Fixed a bug :P

@[inline, reducible] def comp (f: β → γ) (g: α → β): α → γ :=
  λx, f (g x)

@[inline, reducible] def dcomp {β: α → Sort u₂} {γ: Π{x: α}, β x → Sort u₃}
  (f: Π{x: α}, Πy: β x, γ y) (g: Πx, β x): Πx, γ (g x) :=
    λx, f (g x)

infixr ` ∘ `:90  := function.comp
infixr ` ∘' `:80 := function.dcomp

@[reducible] def comp_right (f: β → β → β) (g: α → β): β → α → β :=
  λb, λa, f b (g a)
@[reducible] def comp_left (f: β → β → β) (g: α → β): α → β → β :=
  λa, λb, f (g a) b
@[reducible] def on_fun (f: β → β → γ) (g: α → β): α → α → γ :=
  λx, λy, f (g x) (g y)
@[reducible] def combine (f: α → β → γ) (op: γ → δ → ζ) (g: α → β → δ): α → β → ζ :=
  λx, λy, op (f x y) (g x y)
@[reducible] def const (β: Sort u₂) (a: α): β → α :=
  λx, a
@[reducible] def swap {γ: α → β → Sort u₃} (f: Πx, Πy, γ x y): Πy, Πx, γ x y :=
  λy, λx, f x y
@[reducible] def app {β: α → Sort u₂} (f: Πx, β x) (x: α): β x :=
  f x

lemma left_id (f: α → β): id ∘ f = f := eq.refl f
lemma right_id (f: α → β): f ∘ id = f := eq.refl f
lemma comp_app (f: β → γ) (g: α → β) (a: α): (f ∘ g) a = f (g a) := eq.refl (f (g a))

lemma comp.assoc (f: γ → δ) (g: β → γ) (h: α → β): (f ∘ g) ∘ h = f ∘ (g ∘ h) := eq.refl (f ∘ (g ∘ h))
lemma comp.left_id (f: α → β): id ∘ f = f := left_id f
lemma comp.right_id (f: α → β): f ∘ id = f := right_id f

lemma comp_const_right (f: β → γ) (b: β): f ∘ (const α b) = const α (f b) := eq.refl (const α (f b))

def is_injective(f: α → β) := ∀⦃a₁ a₂: α⦄, f a₁ = f a₂ → a₁=a₂
def injective(α: Sort u₁)(β: Sort u₂): Sort (max 1 (imax u₁ u₂)) := Σ'f: α → β, is_injective f
instance Sort_hookrightarrow_Sort: has_hookrightarrow (Sort u₁) (Sort u₂) (Sort (max 1 (imax u₁ u₂))) :=
  has_hookrightarrow.mk injective
instance Sort_rightarrowtail_Sort: has_rightarrowtail (Sort u₁) (Sort u₂) (Sort (max 1 (imax u₁ u₂))) :=
  has_rightarrowtail.mk injective
instance injective_to_function: has_coe_to_fun (α ↪ β) (λf, α → β) :=
  has_coe_to_fun.mk (λx: α ↪ β, x.fst)
lemma injective.comp (g: β ↪ γ) (f: α ↪ β): α ↪ γ :=
  ⟨(g: β → γ) ∘ (f: α → β),
  λ⦃a₁ a₂: α⦄, λh, f.snd (g.snd h)⟩ --I want to use `implies.trans` there. I can't!
infixr (name := inj_comp_inj) ` ∘ `:90  := function.injective.comp
/- Note to self: You may need more lemmas, the equivalents of `∘`.-/
def is_surjective(f: α → β) := ∀b: β, ∃a: α, f a = b
def surjective(α: Sort u₁)(β: Sort u₂): Sort (max 1 (imax u₁ u₂)) := Σ'f: α → β, is_surjective f
instance Sort_twoheadrightarrow_Sort: has_twoheadrightarrow (Sort u₁) (Sort u₂) (Sort (max 1 (imax u₁ u₂))) :=
  has_twoheadrightarrow.mk surjective
instance surjective_to_function: has_coe_to_fun (α ↠ β) (λf, α → β) :=
  has_coe_to_fun.mk (λx: α ↠ β, x.fst)
lemma surjective.comp (g: β ↠ γ) (f: α ↠ β): α ↠ γ := 
  ⟨(g: β→γ)∘(f: α→β), λc: γ, (do
    let gc: ∃b: β, g b = c := g.snd c,
    let Fb := λb: β, λgbc: g b = c, (do
      let fb: ∃a: α, f a = b := f.snd b,
      let Fa := λa: α, λfab: f a = b, (do
        let gfa_gb: g (f a) = g b := congr_arg g fab,
        let gfa_c: g (f a) = c := eq.trans gfa_gb gbc,
        exists.intro a gfa_c),
      exists.elim fb Fa),
    exists.elim gc Fb)⟩
infixr (name := sur_comp_sur) ` ∘ `:90  := function.surjective.comp
def is_bijective(f: α → β) := is_injective f ∧ is_surjective f
def bijective(α: Sort u₁)(β: Sort u₂): Sort (max 1 (imax u₁ u₂)) := Σ'f: α → β, is_bijective f
instance Sort_twoheadrightarrowtail_Sort: has_twoheadrightarrowtail (Sort u₁) (Sort u₂) (Sort (max 1 (imax u₁ u₂))) :=
  has_twoheadrightarrowtail.mk bijective
instance bijective_to_injective: has_coe (α ⤖ β) (α ↪ β) :=
  has_coe.mk (λf, ⟨f.fst, f.snd.elim_left⟩)
instance bijective_to_surjective: has_coe (α ⤖ β) (α ↠ β) :=
  has_coe.mk (λf, ⟨f.fst, f.snd.elim_right⟩)
instance bijective_to_function: has_coe_to_fun(α ⤖ β) (λf,α → β) :=
  has_coe_to_fun.mk (λf, f.fst)
lemma bijective.comp (g: β ⤖ γ) (f: α ⤖ β): α ⤖ γ :=
  sorry --Blegh, coercion hell
end function