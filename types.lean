prelude
import .operations

universes u v

@[inline] def id_delta {α : Sort u} (a : α) : α := a
abbreviation id_rhs (α : Sort u) (a : α) : α := a

structure product (α: Type u) (β: Type v) :=
  (fst: α)
  (snd: β)
instance Type_times_Type: has_times (Type u) (Type v) (Type max u v) :=
  ⟨product⟩

inductive sum (α: Type u) (β: Type v)
  | inl (val: α) : sum
  | inr (val: β) : sum
instance Type_oplus_Type: has_oplus (Type u) (Type v) (Type max u v) :=
  ⟨sum⟩

structure sigma {α: Type u} (β: α → Type v) :=
  (fst : α)
  (snd : β fst)
notation `Σ` binders `, ` r:(scoped P, sigma P) := r

inductive list (T: Type u)
  | nil: list
  | cons (hd: T) (tl: list) : list
notation `[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := l
instance Type_postfix_mul: has_postfix_mul (Type u) (Type u) :=
  ⟨list⟩