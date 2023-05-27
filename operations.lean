prelude
set_option pp.beta true

noncomputable theory

universes u v w

notation `Prop` := Sort 0
notation `𝔹` := Prop
notation f ` $ `:1 a:0 := f a

@[reducible] def out_param (α: Sort u): Sort u := α

class has_bot(α: out_param $ Sort u) :=
  (bot: α)
notation `⊥` := has_bot.bot
class has_top(α: out_param $ Sort u) :=
  (top: α)
notation `⊤` := has_top.top
class has_emptyc(α: out_param $ Sort u) :=
  (emptyc: α)
notation `∅` := has_emptyc.emptyc
class has_zero(α: Type u) :=
  (zero: α)
class has_one(α: Type u) :=
  (one: α)
--

class has_inv(α: Sort u)(β: out_param $ Sort v) :=
  (inv: α → β)
postfix `⁻¹`:1034 := has_inv.inv
class has_postfix_ast(α: Sort u)(β: out_param $ Sort v) :=
  (postfix_ast: α → β)
postfix `*`:1034 := has_postfix_ast.postfix_ast
class has_postfix_question_mark(α: Sort u)(β: out_param $ Sort v) :=
  (postfix_question_mark: α → β)
postfix `?`:1034 := has_postfix_question_mark.postfix_question_mark

class has_add(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (add: α → β → γ)
infixl ` + `:65 := has_add.add

class has_eq(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (eq: α → β → γ)
infix ` = `:50 := has_eq.eq

class has_lnot(α: Sort u)(β: out_param $ Sort v) :=
  (lnot: α → β)
prefix `¬`:40 := has_lnot.lnot

class has_wedge(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (wedge: α → β → γ)
infixl ` ∧ `:35 := has_wedge.wedge
class has_times(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (times: α → β → γ)
infixl ` × `:35 := has_times.times

class has_vee(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (vee: α → β → γ)
infixl ` ∨ `:30 := has_vee.vee
class has_oplus(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (oplus: α → β → γ)
infixl ` ⊕ `:30 := has_times

class has_lr_arrow(α: Sort u)(β: Sort v)(γ: out_param $ Sort w) :=
  (lr_arrow: α → β → γ)
infix ` ↔ `:20 := has_lr_arrow.lr_arrow

