prelude

import .types

universes u v

noncomputable theory

notation `⊥` :=  ∀p: Prop, p
notation `⊤` := ¬⊥

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
instance Prop_leftrightarrow_Prop: has_leftrightarrow Prop Prop Prop := ⟨iff⟩

def equ {α: Sort u} (a b: α) : Prop := ∀ϕ: α → Prop, ϕ a ↔ ϕ b
instance homo_eq(α: Sort u): has_eq α α Prop := ⟨equ⟩

axiom prop_ext {p q: Prop} : (p↔q) ↔ p=q

def neq {α: Sort u} (a b: α) := ¬(a = b)
instance homo_neq(α: Sort u): has_ne α α Prop := ⟨neq⟩

inductive Exists {α: Sort u} (ϕ: α → Prop) : Prop
  | intro (a: α) (h: ϕ a) : Exists
notation `∃` binders `, ` r:(scoped P, Exists P) := r

def exists_unique {α: Sort u} (ϕ: α → Prop) :=
  ∃ x, ϕ x ∧ ∀ y, ϕ y → y = x
notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

lemma dn_intro {p: Prop} : p → ¬¬p :=
  λhp: p,
    λhnp: ¬p,
      hnp hp
lemma and.elim_left {p q: Prop} : p∧q → p :=
  λh: p ∧ q,
    h.left
lemma and.elim_right {p q: Prop} : p∧q → q :=
  λh: p ∧ q,
    h.right
lemma or.intro_left {p: Prop} (q: Prop) : p → p∨q :=
  λhp: p,
    or.inl hp
lemma or.intro_right (p: Prop) {q: Prop} : q → p∨q :=
  λhq: q,
    or.inr hq
lemma iff.elim_left {p q: Prop} : (p↔q) → p→q :=
  λh: p↔q,
    h.mp
lemma iff.elim_right {p q: Prop} : (p↔q) → q→p :=
  λh: p↔q,
    h.mpr
lemma equ.refl {α: Sort u} (a: α) : a = a :=
  λϕ: α → Prop,
    iff.intro
      (λh: ϕ a, h)
      (λh: ϕ a, h)
lemma equ.symm {α: Sort u} {a b: α}: a = b → b = a :=
  λh: a = b,
    λϕ: α → Prop,
      iff.intro
        (h ϕ).mpr
        (h ϕ).mp
lemma equ.trans {α: Sort u} {a b c: α}: a = b → b = c → a = c :=
  λh₁: a = b,
    λh₂: b = c,
      λϕ: α → Prop,
        iff.intro
          (λhpa: ϕ a, (h₂ ϕ).mp ((h₁ ϕ).mp hpa)) --ϕ a → ϕ c
          (λhpc: ϕ c, (h₁ ϕ).mpr ((h₂ ϕ).mpr hpc))--ϕ c → ϕ a
lemma equ.subst {α: Sort u} (P: α → Prop) {a b: α}: a = b → (P a ↔ P b) := 
  λh: a = b,
    h P
infixr ` ▸ `:75 := equ.subst
lemma equ.comm {α: Sort u} {a b: α}: a=b ↔ b=a :=
  iff.intro (λh: a=b, equ.symm h) (λh: b=a, equ.symm h)
--
def trivial: ⊤ := 
  λf: ⊥, f
def implies (p q: Prop) := p → q
lemma implies.trans {p q r: Prop} : (p→q) → (q→r) → (p→r) := 
  λh₁: p→q,
    λh₂: q→r,
      λhp: p,
        h₂ (h₁ hp)
def absurd {p: Prop} (h₁: p) (h₂: ¬p) (q: Prop) : q :=
  h₂ h₁ q
lemma mt {p q: Prop} : (p → q) → (¬q → ¬p) :=
  λh: p → q,
    λhnq: ¬q,
      λhp: p,
        hnq (h hp)
lemma not_false: ¬⊥ := trivial
lemma equ.mp {α β: Sort u} : (α = β) → (α → β) := sorry
lemma equ.mpr {α β: Sort u} : (α = β) → (β → α) :=
  λh: α = β,
    equ.mp (equ.symm h) --Unsure
lemma equ.substr {α: Sort u} {P: α → Prop} {a b: α} : a = b → P a → P b := sorry
lemma congr {α: Sort u} {β: Sort v} {f g: α → β} {a b: α}: f = g → a = b → f a = g b :=
  λh₁: f = g,
    λh₂: a = b,
      λϕ: β → Prop,
        iff.intro
          (λhpfa: ϕ (f a), (h₂ (λa', ϕ (g a'))).mp ((h₁ (λf', ϕ (f' a))).mp hpfa)) --Leibnizian
          (λhpgb: ϕ (g b), (h₂ (λb', ϕ (f b'))).mpr ((h₁ (λg', ϕ (g' b))).mpr hpgb)) --Chicanery

lemma congr_fun {α: Sort u} {β: α → Sort v} {f g: Πx, β x} (h: f = g) (a: α) :
  f a = g a := sorry
lemma congr_arg {α: Sort u} {β: Sort v} {a b: α} (f: α → β) : a = b → f a = f b :=
  congr (equ.refl f)
lemma trans_rel_left {α: Sort u} {a b c: α} (r: α → α → Prop) : r a b → b = c → r a c :=
  λh₁: r a b,
    λh₂: b = c,
      (h₂ (λx, r a x)).mp h₁
lemma trans_rel_right {α: Sort u} {a b c: α} (r: α → α → Prop) : a = b → r b c → r a c :=
  λh₁: a = b,
    λh₂: r b c,
      (h₁ (λx, r x c)).mpr h₂
lemma of_eq_true {p: Prop} (h: p = ⊤) : p := equ.mpr h trivial
lemma not_of_eq_false {p: Prop} (h: p = ⊥) : ¬p := equ.mp h
