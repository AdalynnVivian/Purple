prelude
set_option pp.beta true

noncomputable theory
 
universes u v w


notation `Prop` := Sort 0
notation f ` $ `:1 a:0 := f a
@[reducible] def out_param (α : Sort u) : Sort u := α

section --"NORMAL" operators
  variables (α: Sort u) (β: Sort v) (γ: out_param $ Sort w)
  reserve infix ` ↔ `:20
    class has_leftrightarrow :=
      (leftrightarrow: α → β → γ)
    infix ` ↔ ` := has_leftrightarrow.leftrightarrow
  --
  reserve infixr ` ⟶ `:25
    class has_longrightarrow :=
      (longrightarrow: α → β → γ)
    infixr ` ⟶ ` := has_longrightarrow.longrightarrow 
  reserve infixr ` ↣ `:25
    class has_rightarrowtail :=
      (rightarrowtail: α → β → γ)
    infixr ` ↣ ` := has_rightarrowtail.rightarrowtail
  reserve infixr ` ↪ `:25
    class has_hookrightarrow :=
      (hookrightarrow: α → β → γ)
    infixr ` ↪ ` := has_hookrightarrow.hookrightarrow
  reserve infixr ` ↠ `:25
    class has_twoheadrightarrow :=
      (twoheadrightarrow: α → β → γ)
    infixr ` ↠ ` := has_twoheadrightarrow.twoheadrightarrow
  reserve infixr ` ⤖ `:25
    class has_twoheadrightarrowtail :=
      (twoheadrightarrowtail: α → β → γ)
    infixr ` ⤖ ` := has_twoheadrightarrowtail.twoheadrightarrowtail
  reserve infixr ` ⇒ `:25
    class has_Rightarrow :=
      (Rightarrow: α → β → γ)
    infixr ` ⇒ ` := has_Rightarrow.Rightarrow
  --
  reserve infixl ` ⊕ `:30 --Note to self: Figure out 
    class has_oplus := --How to get A ⊕ B ⊕ C
      (oplus: α → β → γ) --To have π₁ π₂ π₃
    infixl ` ⊕ ` := has_oplus.oplus
  reserve infixl ` ∨ `:30
    class has_vee :=
      (vee: α → β → γ)
    infixl ` ∨ ` := has_vee.vee
  --
  reserve infixl ` × `:35
    class has_times :=
      (times: α → β → γ)
    infixl ` × ` := has_times.times
  reserve infixl ` ∧ `:35
    class has_wedge :=
      (wedge: α → β → γ)
    infixl ` ∧ ` := has_wedge.wedge
  --
  reserve prefix `¬`:40
    class has_lnot :=
      (lnot: α → γ)
    prefix `¬` := has_lnot.lnot
  --
  reserve infix ` = `:50
    class has_eq :=
      (eq: α → β → γ)
    infix ` = ` := has_eq.eq
  reserve infix ` ≠ `:50
    class has_ne :=
      (ne: α → β → γ)
    infix ` ≠ ` := has_ne.ne
  reserve infix ` ≅ `:50
    class has_cong :=
      (cong: α → β → γ)
    infix ` ≅ ` := has_cong.cong
  reserve infix ` ∈ `:50
    class has_mem :=
      (mem: α → β → γ)
    infix ` ∈ ` := has_mem.mem
  reserve infix ` ∉ `:50
    class has_nmem :=
      (nmem: α → β → γ)
    infix ` ∉ ` := has_nmem.nmem
  reserve infix ` ∋ `:50
    class has_contains :=
      (contains: α → β → γ)
    infix ` ∋ ` := has_contains.contains
  reserve infix ` ∌ `:50
    class has_ncontains :=
      (ncontains: α → β → γ)
    infix ` ∌ ` := has_ncontains.ncontains
  reserve infix ` < `:50
    class has_lt :=
      (lt: α → β → γ)
    infix ` < ` := has_lt.lt
  reserve infix ` ≤ `:50
    class has_le :=
      (le: α → β → γ)
    infix ` ≤ ` := has_le.le
  reserve infix ` > `:50
    class has_gt :=
      (gt: α → β → γ)
    infix ` > ` := has_gt.gt
  reserve infix ` ≥ `:50
    class has_ge :=
      (ge: α → β → γ)
    infix ` ≥ ` := has_ge.ge
  reserve infix ` ⊂ `:50
    class has_ssubset :=
      (ssubset: α → β → γ)
    infix ` ⊂ ` := has_ssubset.ssubset
  reserve infix ` ⊆ `:50
    class has_subset :=
      (subset: α → β → γ)
    infix ` ⊆ ` := has_subset.subset
  reserve infix ` ⊃ `:50
    class has_ssupset :=
      (ssupet: α → β → γ)
    infix ` ⊃ ` := has_ssupset.ssupset
  reserve infix ` ⊇ `:50
    class has_supset :=
      (supset: α → β → γ)
    infix ` ⊇ ` := has_supset.supset
  reserve infix ` ◁ `:50
    class has_npropsub :=
      (npropsub: α → β → γ)
    infix ` ◁ ` := has_npropsub.nprobsub
  reserve infix ` ⊴ `:50
    class has_nsub :=
      (nsub: α → β → γ)
    infix ` ⊴ ` := has_nsub.nsub
  reserve infix ` ▷ `:50
    class has_npropsup :=
      (npropsup: α → β → γ)
    infix ` ▷ ` := has_npropsub.npropsub
  reserve infix ` ⊵ `:50
    class has_nsup :=
      (nsup: α → β → γ)
    infix ` ⊵ ` := has_nsup.nsup
  reserve infix ` ∣ `:50
    class has_dvd :=
      (dvd: α → β → γ)
    infix ` ∣ ` := has_dvd.dvd
--
  reserve infixl ` + `:65
    class has_add :=
      (add: α → β → γ)
    infixl ` + ` := has_add.add
  reserve infixl ` - `:65
    class has_sub :=
      (sub: α → β → γ)
    infixl ` - ` := has_sub.sub
  reserve infixl ` ∪ `:65
    class has_union :=
      (union: α → β → γ)
    infixl ` ∪ ` := has_union.union
  reserve prefix `⋂`:65
    class has_bInter :=
      (bInter: α → γ)
    prefix `⋂` := has_bInter.bInter
--
  reserve infixl ` * `:70
    class has_mul :=
      (mul: α → β → γ)
    infixl ` * ` := has_mul.mul
  reserve infixl ` ⬝ `:70
    class has_cdot :=
      (cdot: α → β → γ)
    infixl ` ⬝ ` := has_cdot.cdot
  reserve infixl ` ∗ `:70
    class has_ast :=
      (ast: α → β → γ)
    infixl ` ∗ ` := has_ast.ast 
  reserve infixl ` / `:70
    class has_frac :=
      (frac: α → β → γ)
    infixl ` / ` := has_frac.frac
  reserve infixl ` ÷ `:70
    class has_div :=
      (div: α → β → γ)
    infixl ` ÷ ` := has_div.div 
  reserve infixl ` ∩ `:70
    class has_inter :=
      (inter: α → β → γ)
    infixl ` ∩ ` := has_inter.inter
  reserve infix  ` \ `:70
    class has_sdiff :=
      (sdiff: α → β → γ)
    infix ` \ ` := has_sdiff.sdiff
  reserve prefix `⋃`:70
    class has_bUnion :=
      (bUnion: α → β → γ)
    prefix `⋃` := has_bUnion.bUnion
--  
  reserve prefix `-`:75
    class has_neg :=
      (neg: α → γ)
    prefix `-` := has_neg.neg
  reserve prefix `+`:75
    class has_pos :=
      (pos: α → γ)
    prefix `+` := has_pos.pos
--
  reserve postfix `!`:76
    class has_factorial :=
      (factorial: α → β → γ)
    postfix `!` := has_factorial.factorial
--
  reserve infixr ` ^ `:80
    class has_exp :=
      (exp: α → β → γ)
    infixr ` ^ ` := has_exp.exp
--
  reserve infixl ` ∘ `:90
    class has_comp :=
      (comp: α → β → γ)
  infixl ` ∘ ` := has_comp.comp 
  --
  reserve prefix `𝒫`:100
    class has_pow :=
      (pow: α → γ)
    prefix `𝒫` := has_pow.pow
  --
  reserve postfix `⁻¹`:1034
    class has_inv :=
      (inv: α → γ)
    postfix `⁻¹` := has_inv.inv
  reserve postfix `ᶜ`:1034
    class has_com :=
      (com: α → β → γ)
    postfix `ᶜ` := has_comp.comp
end
-- Empty set `\
class has_emptyc (α: Sort u) := (emptyc: α)
notation `∅` := has_emptyc.emptyc
-- `0` and `1` for groups
class has_zero (α: Sort u) := (zero: α)
class has_one (α: Sort u) := (one: α)
-- {a} {a,b} ...
class has_singleton (α: Sort u) (γ: out_param $ Sort w) :=
  (singleton: α → γ)
class has_insert (α: Sort u) (β: Sort v) (γ: out_param $ Sort w) :=
  (insert: α → β → γ)
-- (a,b)
/- Keep getting errors with this one! 
-/
instance: has_singleton Prop Prop := ⟨sorry⟩
instance: has_insert Prop Prop Prop := ⟨sorry⟩

constant p: Prop
instance: has_add Prop Prop Prop := ⟨sorry⟩

#check p+p