prelude

import .operations

universes u v w

@[inline] def id_delta {α: Sort u} (a: α): α :=
  a
@[reducible] def opt_param (α: Sort u) (default: α): Sort u :=
  α
abbreviation id_rhs (α: Sort u) (a: α): α := a

inductive punit: Sort u
  | star: punit
abbreviation unit: Type := punit
@[pattern] abbreviation unit.star: unit := punit.star

@[reducible] def thunk (α: Type u): Type u :=
  unit → α

inductive true: 𝔹
  | intro: true
instance top_Prop: has_top 𝔹 :=
  has_top.mk true
inductive false: 𝔹
instance bot_Prop: has_bot 𝔹 :=
  has_bot.mk false
inductive empty: Type
instance emptyc_Type: has_emptyc Type := has_emptyc.mk empty

def not (p: 𝔹): 𝔹 := p → ⊥
instance not_Prop: has_lnot 𝔹 𝔹 := has_lnot.mk not

inductive eq {α: Sort u} (a: α): α → 𝔹
  | refl []: eq a
instance homo_eq(α: Sort u): has_eq α α 𝔹 :=
  has_eq.mk eq

inductive heq {α: Sort u} (a: α): Π{β: Sort u}, β → 𝔹
  | refl []: heq a
infix ` == `:50 := heq

--`prod'` is used instead of `prod` to allow overloading `(a, b)` 
structure prod' (α: Type u) (β: Type v) := 
  (fst: α)
  (snd: β)
instance Type_times_Type: has_times (Type u) (Type v) (Type max u v) :=
  has_times.mk prod'
structure pprod (α: Sort u) (β: Sort v) :=
  (fst: α)
  (snd: β)
infixl ` ×' `:35 := pprod

structure and (p: 𝔹) (q: 𝔹): 𝔹 := intro ::
  (fst: p)
  (snd: q)
instance Prop_wedge_Prop: has_wedge 𝔹 𝔹 𝔹 :=
  has_wedge.mk and
lemma and.elim_left {p q: 𝔹} (h: p ∧ q): p := h.1
lemma and.elim_right {p q: 𝔹} (h: p ∧ q): q := h.2

attribute [refl] eq.refl

@[pattern] def rfl {α: Sort u} {a: α}: a = a := eq.refl a
@[elab_as_eliminator, subst] lemma eq.subst {α: Sort u} {P: α → 𝔹} {a b: α} (e: a = b) (h: P a) : P b :=
  eq.rec h e
infixr ` ▸ `:75 := eq.subst

@[trans] lemma eq.trans {α: Sort u} {a b c: α} (h₁: a = b) (h₂: b = c): a = c :=
  h₂ ▸ h₁
@[symm] lemma eq.symm {α: Sort u} {a b: α} (h: a = b): b = a :=
  h ▸ rfl

@[pattern] def heq.rfl {α : Sort u} {a : α} : a == a := heq.refl a

lemma eq_of_heq {α: Sort u} {a a': α} (h: a == a'): a = a' :=
have ∀ (α': Sort u) (a': α') (h₁: @heq α a α' a') (h₂ : α = α'), (eq.rec_on h₂ a : α') = a', from
  λ (α': Sort u) (a': α') (h₁: @heq α a α' a'), heq.rec_on h₁ (λ h₂: α = α, rfl),
show (eq.rec_on (eq.refl α) a : α) = a', from
  this α a' h (eq.refl α)

--Removed inj for prod

inductive sum (α: Type u) (β: Type v)
| inl (val: α): sum
| inr (val: β): sum
instance Type_oplus_Type: has_oplus (Type u) (Type v) (Type max u v) :=
  has_oplus.mk sum
inductive psum (α: Sort u) (β: Sort v)
| inl (val: α): psum
| inr (val: β): psum
infixl ` ⊕' `:30 := psum

inductive or (p q: 𝔹) : 𝔹
| inl (h: p): or
| inr (h: q): or
instance Prop_vee_Prop: has_vee 𝔹 𝔹 𝔹 :=
  has_vee.mk or
lemma or.intro_left {a: 𝔹} (b: 𝔹) (h: a): a∨b :=
  or.inl h
lemma or.intro_right (a: 𝔹) {b: 𝔹} (h: b): a∨b :=
  or.inr h 

structure sigma {α: Type u} (β: α → Type v) :=
  (fst: α)
  (snd: β fst)
notation `Σ` binders `, ` r:(scoped P, sigma P) := r
structure psigma {α: Sort u} (β: α → Sort v) :=
  (fst: α)
  (snd: β fst)
notation `Σ'` binders `, ` r:(scoped P, psigma P) := r

structure subtype {α: Sort u} (ϕ: α → 𝔹) :=
  (val: α) (property: ϕ val)

inductive option (α: Type u)
  | none: option
  | some (val: α): option
instance Type_postfix_question_mark: has_postfix_question_mark (Type u) (Type u) :=
  has_postfix_question_mark.mk option

export option (none some)

inductive list (T: Type u)
  | nil: list
  | cons (hd: T) (tl: list): list
instance Type_postfix_ast: has_postfix_ast (Type u) (Type u) :=
  has_postfix_ast.mk list
notation `[` a `, ` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := list.cons a l

inductive nat
  | zero: nat
  | succ(n: nat): nat
notation `ℕ` := nat
namespace nat
  protected def add: ℕ → ℕ → ℕ
    | a zero := a
    | a (succ b) := succ (add a b)
  attribute [pattern] nat.add nat.add._main
end nat
instance nat_has_zero: has_zero ℕ := has_zero.mk nat.zero
instance nat_has_one: has_one ℕ := has_one.mk (nat.succ nat.zero)
instance nat_add_nat: has_add ℕ ℕ ℕ := has_add.mk nat.add

lemma nat_add_zero (n: ℕ): n + 0 = n := eq.refl n