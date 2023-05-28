prelude

import .operations
import .core

set_option pp.beta true
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
  variable {p: 𝔹}

  lemma ne_false_of_self: p → p≠⊥ :=
    λhp: p, λheq: p = ⊥, heq ▸ hp
  lemma ne_true_of_not: ¬p → p≠⊤ :=
    λhnp: ¬p, λhpet: p=⊤, absurd (eq.mpr hpet trivial) hnp
  lemma true_ne_false: ⊤ ≠ ⊥ :=
    ne_false_of_self trivial
end

variables {a b c d: 𝔹}

lemma and.elim (h₁: a ∧ b) (h₂: a → b → c): c :=
  h₂ h₁.elim_left h₁.elim_right
lemma and.swap: a ∧ b → b ∧ a :=
  λh, and.intro h.elim_right h.elim_left
lemma and.symm: a ∧ b → b ∧ a := 
  and.swap

lemma or.elim (h₁: a ∨ b) (h₂: a → c) (h₃: b → c): c :=
  or.rec h₂ h₃ h₁
lemma non_contradictory_em (a: 𝔹) : ¬¬(a ∨ ¬a) :=
  λh: ¬(a ∨ ¬a),
    absurd
      (λha: a, h (or.inl ha))
      (λhna: ¬a, h (or.inr hna))
lemma or.swap: a ∨ b → b ∨ a :=
  or.rec or.inr or.inl
lemma or.symm: a ∨ b → b ∨ a :=
  or.swap

def xor (p q : 𝔹) := (p ∧ ¬q) ∨ (q ∧ ¬p)

structure iff (p q: 𝔹): 𝔹 := intro ::
  (mp: p → q)
  (mpr: q → p)
instance Prop_lr_arrow_Prop: has_leftrightarrow 𝔹 𝔹 𝔹 :=
  has_leftrightarrow.mk iff

lemma iff.elim: ((a → b) → (b → a) → c) → (a↔b) → c :=
  λh₁, λh₂, h₁ h₂.mp h₂.mpr
lemma iff.elim_left: (a ↔ b) → a → b := iff.mp
lemma iff.elim_right: (a ↔ b) → b → a := iff.mpr
lemma iff_iff_implies_and_implies (p q: 𝔹): (p↔q) ↔ (p→q) ∧ (q→p) :=
  iff.intro (λh, and.intro h.mp h.mpr) (λh, iff.intro h.elim_left h.elim_right)

@[refl] lemma iff.refl (p: 𝔹): p↔p :=
  iff.intro (λhp, hp) (λhp, hp)
lemma iff.rfl {p: 𝔹}: p↔p :=
  iff.refl p

@[trans] lemma iff.trans (h₁: a↔b) (h₂: b↔c): a↔c :=
  iff.intro
    (implies.trans h₁.mp h₂.mp)
    (implies.trans h₂.mpr h₁.mpr)
@[symm] lemma iff.symm (h: a↔b): b↔a :=
  iff.intro h.mpr h.mp
lemma iff.comm: (a↔b)↔(b↔a) :=
  iff.intro (@iff.symm a b) (@iff.symm b a)
lemma eq.to_iff {p q: 𝔹} (h: p=q): p↔q :=
  h ▸ iff.refl p
lemma neq_of_not_iff {p q: 𝔹}: ¬(p↔q) → p≠q :=
  mt eq.to_iff
lemma not_iff_not_of_iff (h: a↔b): ¬a↔¬b :=
  iff.intro (mt h.mpr) (mt h.mp)
lemma of_iff_true (h: a↔⊤): a :=
  h.mpr trivial
lemma not_of_iff_false: (a↔⊥)→¬a :=
  iff.mp
lemma iff_true_intro (h: a): a↔⊤ :=
  iff.intro (λx, trivial) (λx, h)
lemma iff_false_intro (h: ¬a): a↔⊥ :=
  iff.intro h (false.rec a)
lemma not_non_contradictory_iff_absurd (p: 𝔹): ¬¬¬p ↔ ¬p :=
  iff.intro
    (λhn3p: ¬¬¬p, λhp: p, hn3p (non_contradictory_intro hp))
    (@non_contradictory_intro ¬p)
lemma imp_congr (h₁: a↔c) (h₂: b↔d): (a→b)↔(c→d) :=
  iff.intro
    (λh, implies.trans h₁.mpr (implies.trans h h₂.mp))
    (λh, implies.trans h₁.mp (implies.trans h h₂.mpr))
lemma imp_congr_ctx (h₁: a↔c) (h₂: c→(b↔d)): (a→b) ↔ (c→d) :=
  iff.intro
    (λh, λhc, (h₂ hc).mp (h (h₁.mpr hc)))
    (λh, λha, (h₂ (h₁.mp ha)).mpr (h (h₁.mp ha)))
lemma imp_congr_right (h: a→(b↔c)): (a→b) ↔ (a→c) :=
  iff.intro
    (λhab, λha, (h ha).mp (hab ha))
    (λhac, λha, (h ha).mpr (hac ha))
lemma not_not_intro (ha: a): ¬¬a :=
  non_contradictory_intro ha
lemma nont_of_not_not_not (h: ¬¬¬a): ¬a :=
  (not_non_contradictory_iff_absurd a).mp h
@[simp] lemma not_true: ¬⊤ ↔ ⊥ := 
  iff_false_intro (not_not_intro trivial)
@[simp] lemma not_false_iff: ¬⊥ ↔ ⊤ :=
  iff_true_intro not_false
lemma not_congr (h: a↔b): ¬a ↔ ¬b :=
  not_iff_not_of_iff h
lemma ne_self_iff_false {α: Sort u} (a: α): a≠a ↔ ⊥ :=
  iff.intro false_of_ne false.elim
@[simp] lemma eq_self_iff_true {α: Sort u} (a: α): a=a ↔ ⊤ :=
  iff_true_intro (eq.refl a)
@[simp] lemma iff_not_self (p: 𝔹): (p↔¬p)↔⊥ :=
  iff_false_intro (λh: p↔¬p,
    let not_p: ¬p := λhp:p, h.mp hp hp in
      not_p (h.mpr not_p)
  )
@[simp] lemma not_iff_self (p: 𝔹): (¬p↔p)↔⊥ :=
  iff.trans iff.comm (iff_not_self p)
lemma true_iff_false: (⊤↔⊥)↔⊥ :=
  iff_false_intro (λh, iff.mp h trivial)
lemma false_iff_true: (⊥↔⊤)↔⊥ :=
  iff.trans iff.comm true_iff_false
lemma false_of_true_iff_false: (⊤↔⊥)→⊥ :=
  true_iff_false.mp
lemma false_of_true_eq_false: (⊤=⊥)→⊥ :=
  λh, h ▸ trivial
lemma true_eq_false_of_false: ⊥→(⊤=⊥) :=
  false.elim

lemma eq_comm {α: Sort u} {a b: α}: a=b↔b=a :=
  iff.intro eq.symm eq.symm

/-! and simp rules -/
lemma and.imp (hac: a→c) (hbd: b→d): a∧b → c∧d :=
  λh, and.intro (hac h.elim_left) (hbd h.elim_right)
lemma and_implies (hac: a→c) (hbd: b→d): a∧b → c∧d :=
  and.imp hac hbd
lemma and_congr (h₁: a↔c) (h₂: b↔d): (a∧b) ↔ (c∧d) :=
  iff.intro (and.imp h₁.mp h₂.mp) (and.imp h₁.mpr h₂.mpr)
lemma and_congr_right (h: a→(b↔c)): (a∧b) ↔ (a∧c) :=
  iff.intro
    (λhab, and.intro hab.elim_left ((h hab.elim_left).mp hab.elim_right))
    (λhac, and.intro hac.elim_left ((h hac.elim_left).mpr hac.elim_right))
lemma and.comm: a∧b ↔ b∧a :=
  iff.intro and.swap and.swap
lemma and_comm (p q: 𝔹): p ∧ q ↔ q ∧ p := and.comm
lemma and.assoc: (a∧b)∧c ↔ a∧(b∧c) :=
  iff.intro
    (λh, and.intro h.elim_left.elim_left (and.intro h.elim_left.elim_right h.elim_right))
    (λh, and.intro (and.intro h.elim_left h.elim_right.elim_left) h.elim_right.elim_right)
lemma and_assoc (p q: 𝔹): (p∧q)∧c ↔ p∧(q∧c) := and.assoc
lemma and.left_comm: a∧(b∧c) ↔ b∧(a∧c) :=
  iff.trans
    and.assoc.symm
    (iff.trans (and_congr and.comm (iff.refl c)) and.assoc)
lemma and_iff_left {p q: 𝔹} (hq: q): (p∧q) ↔ p :=
  iff.intro and.elim_left (λhp: p, and.intro hp hq)
lemma and_iff_right {p q: 𝔹} (hp: p): (p∧q) ↔ q :=
  iff.trans and.comm (and_iff_left hp)
@[simp] lemma and_true (p: 𝔹): p∧⊤ ↔ p :=
  and_iff_left trivial
@[simp] lemma true_and (p: 𝔹): ⊤∧p ↔ p :=
  and_iff_right trivial
@[simp] lemma and_false (p: 𝔹): p∧⊥ ↔ ⊥ :=
  iff_false_intro and.elim_right
@[simp] lemma false_and (p: 𝔹): ⊥∧p ↔ ⊥ :=
  iff.trans and.comm (and_false p)
@[simp] lemma not_and_self (p: 𝔹): (¬p ∧ p) ↔ ⊥ :=
  iff.intro (λh, absurd h.elim_right h.elim_left) (false.rec (¬p∧p))
@[simp] lemma and_not_self (p: 𝔹): (p ∧ ¬p) ↔ ⊥ :=
  iff.trans and.comm (not_and_self p)
@[simp] lemma and_self (p: 𝔹): p ∧ p ↔ p :=
  iff.intro and.elim_left (λhp, and.intro hp hp)

/-! or simp rules -/
lemma or.imp (hac: a→c) (hbd: b→d): a∨b → c∨d :=
  or.rec (λha, or.inl (hac ha)) (λhb, or.inr (hbd hb))
lemma or.imp_left (h: a→b): a∨c → b∨c :=
  or.imp h id
lemma or.imp_right (h:a→b): c∨a → c∨b :=
  or.imp id h
lemma or_congr (hac: a↔c) (hbd: b↔d): a∨b ↔ c∨d :=
  iff.intro (or.imp hac.mp hbd.mp) (or.imp hac.mpr hbd.mpr)
lemma or.comm: a∨b ↔ b∨a :=
  iff.intro or.swap or.swap
lemma or_comm (p q: 𝔹): p∨q ↔ q∨p := or.comm
lemma or.assoc: (a∨b)∨c ↔ a∨(b∨c) :=
  iff.intro
    (or.rec (or.imp_right or.inl) (λh, or.inr $ or.inr h))
    (or.rec (λh, or.inl $ or.inl h) (or.imp_left or.inr))
lemma or_assoc (p q: 𝔹): (p∨q)∨c ↔ p∨(q∨c) := or.assoc
lemma or.left_com: a∨(b∨c) ↔ b∨(a∨c) := 
  iff.trans
    (or.assoc.symm)
    (iff.trans (or_congr or.comm (iff.refl c)) or.assoc)
theorem or_iff_right_of_imp (ha: a → b): a∨b ↔ b :=
  iff.intro (or.rec ha id) or.inr 
theorem or_iff_left_of_imp (hb: b → a): a∨b ↔ a :=
  iff.trans or.comm $ or_iff_right_of_imp hb
@[simp] lemma or_true (p: 𝔹): p∨⊤ ↔ ⊤ := 
  iff.intro (or.rec (λhp, trivial) id) or.inr
@[simp] lemma true_or (p: 𝔹): ⊤∨p ↔ ⊤ := 
  iff.trans or.comm $ or_true p
@[simp] lemma or_false (p: 𝔹): p∨⊥ ↔ p :=
  iff.intro (or.rec id false.elim) or.inl
@[simp] lemma false_or (p: 𝔹): ⊥∨p ↔ p :=
  iff.trans or.comm $ or_false p
@[simp] lemma or_self (p: 𝔹): p∨p ↔ p := 
  iff.intro (or.rec id id) or.inl
lemma not_or {p q: 𝔹}: ¬p → ¬q → ¬(p ∨ q) :=
  λhnp, λhnq, λhpq: p∨q,
    or.rec hnp hnq hpq

/-! or resolution rules -/

lemma or.resolve_left {p q: 𝔹} (h: p ∨ q) (np: ¬p): q :=
  or.rec (λhp, false.elim (np hp)) (λhq, hq) h 
lemma or.neg_resolve_left {p q: 𝔹} (h: ¬p ∨ q) (hp: p): q :=
  or.rec (λnp, false.elim (np hp)) (λhq, hq) h
lemma or.resolve_right {p q: 𝔹} (h: p ∨ q) (nq: ¬q): p :=
  or.rec (λhp, hp) (λhq, false.elim (nq hq)) h
lemma or.neg_resolve_right {p q: 𝔹} (h: p ∨ ¬q) (hq: q): p :=
  or.rec (λhp, hp) (λnq, false.elim (nq hq)) h

/-! iff simp rules -/

@[simp] lemma iff_true (p: 𝔹): (p↔⊤)↔p :=
  iff.intro (λh, h.mpr trivial) iff_true_intro
@[simp] lemma true_iff (p: 𝔹): (⊤↔p)↔p :=
  iff.trans iff.comm $ iff_true p 
@[simp] lemma iff_false (p: 𝔹): (p↔⊥)↔¬p :=
  iff.intro iff.mp iff_false_intro
@[simp] lemma false_iff (p: 𝔹): (⊥↔p)↔¬p :=
  iff.trans iff.comm $ iff_false p
@[simp] lemma iff_self (p: 𝔹): (p↔p)↔⊤ :=
  iff.intro (λ_, trivial) (λ_, iff.refl p)
lemma iff_congr (hac: a↔c) (hbd: b↔d): (a↔b) ↔ (c↔d) :=
  iff.intro
    (λhab, iff.trans hac.symm $ iff.trans hab hbd)
    (λhcd, iff.trans hac $ iff.trans hcd hbd.symm)

/-! implies simp rule -/
@[simp] lemma implies_true_iff (α: Sort u): (α→⊤) ↔ ⊤ :=
  iff.intro (λ_, trivial) (λ_, λ_, trivial)
lemma false_implies_iff (p: 𝔹): (⊥→p) ↔ ⊤ :=
  iff.intro (λ_, trivial) (λ_, λh, false.elim h) 
theorem true_implies_iff (p: 𝔹): (⊤→p) ↔ p :=
  iff.intro (λh, h trivial) (λhp, λ_, hp)

/-! existential quantifier -/
inductive Exists {α: Sort u} (p: α → 𝔹): 𝔹
  | intro (w: α) (h: p w): Exists
attribute [intro] Exists.intro

notation `∃` binders `, ` r:(scoped P, Exists P) := r
@[pattern] def exists.intro {α: Sort u} {p: α → 𝔹} (w: α) (h: p w): ∃x, p x := Exists.intro w h

lemma exists.elim {α: Sort u} {p: α → 𝔹} {b: 𝔹}
  (h₁: ∃x, p x) (h₂: ∀a: α, p a → b): b :=
    Exists.rec h₂ h₁

/-! exists unique -/

def exists_unique {α: Sort u} (p: α → 𝔹) :=
  ∃x: α, p x ∧ ∀y: α, p y → y = x
notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

@[intro]
lemma exists_unique.intro {α: Sort u} {p: α → 𝔹} (w: α) (h₁: p w) (h₂: ∀y, p y → y = w) : ∃!x, p x :=
  exists.intro w $ and.intro h₁ h₂

attribute [recursor 4]
lemma exists_unique.elim {α: Sort u} {p: α → 𝔹} {b: 𝔹} (h₂: ∃!x, p x) (h₁: ∀x, p x → (∀y, p y → y=x) → b): b :=
  exists.elim h₂ (λx, λhu, h₁ x hu.elim_left hu.elim_right)

lemma exists_unique_of_exists_of_unique {α: Sort u} {p: α → 𝔹}
  (hex: ∃x, p x) (hu: ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂): ∃!x, p x :=
    exists.elim hex (λx, λpx, 
      exists_unique.intro x px $ λy, λpy, eq.symm (hu x y px py))

lemma unique_of_exists_unique {α: Sort u} {p: α → 𝔹}
  (h: ∃! x, p x) {y₁ y₂: α} (py₁: p y₁) (py₂: p y₂): y₁ = y₂ :=
    h.elim (λx, λpx, λfy, eq.trans (fy y₁ py₁) (fy y₂ py₂).symm)

lemma exists_of_exists_unique {α: Sort u} {p: α → 𝔹} (h: ∃!x, p x): ∃ x, p x :=
  exists.elim h (λa, λhu, exists.intro a hu.elim_left)

/-! exists, forall, exists unique congruences -/
@[congr] lemma forall_congr {α: Sort u} {p q: α → 𝔹} (h: ∀a, p a ↔ q a): (∀a, p a) ↔ (∀a, q a) :=
  iff.intro
    (λhpa, λa, (h a).mp $ hpa a)
    (λhqa, λa, (h a).mpr $ hqa a)
lemma exists_imp_exists {α: Sort u} {p q: α → 𝔹} (h: ∀a, (p a → q a)) (j: ∃a, p a): ∃a, q a :=
  exists.elim j (λa, λpa, exists.intro a $ h a pa)
lemma exists_congr {α: Sort u} {p q: α → 𝔹} (h: ∀a, p a ↔ q a): (∃a, p a) ↔ (∃a, q a) :=
  iff.intro (exists_imp_exists (λa, (h a).mp)) (exists_imp_exists (λa, (h a).mpr))
lemma exists_unique_congr {α: Sort u} {p₁ p₂: α → 𝔹} (h: ∀x, p₁ x ↔ p₂ x): (∃!x, p₁ x) ↔ (∃!x, p₂ x) :=
  exists_congr (λx, and_congr (h x) (forall_congr (λy, imp_congr (h y) iff.rfl)))
lemma forall_not_of_exists {α: Sort u} {p: α → 𝔹}: ¬(∃x, p x) → (∀x, ¬p x) :=
  λne, λx, λpx, absurd (exists.intro x px) ne

/-! propositional extensionality -/
axiom propext {a b : 𝔹} : (a↔b) → (a=b)

lemma forall_congr_eq {a: Sort u} {p q: a → 𝔹} (h: ∀x, p x = q x): (∀x, p x) = (∀x, q x) :=
  propext $ forall_congr (λa, (h a).to_iff)

lemma imp_congr_eq {a b c d: 𝔹} (h₁: a=c) (h₂: b=d): (a→b) = (c→d) :=
  propext $ imp_congr h₁.to_iff h₂.to_iff

lemma imp_congr_ctx_eq {a b c d: 𝔹} (h₁: a = c) (h₂: c → (b=d)): (a→b) = (c→d) :=
  propext $ imp_congr_ctx h₁.to_iff (λhc, (h₂ hc).to_iff)

lemma eq_true_intro {a: 𝔹} (h: a): a=⊤ :=
  propext $ iff_true_intro h

lemma eq_false_intro {a: 𝔹} (h: ¬a): a=⊥ :=
  propext $ iff_false_intro h

theorem iff.to_eq {a b: 𝔹} (h: a↔b): a=b :=
  propext $ h

theorem iff_eq_eq {a b: 𝔹}: (a↔b) = (a=b) :=
  propext $ iff.intro iff.to_eq eq.to_iff
