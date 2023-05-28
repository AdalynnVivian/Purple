prelude

import .operations
import .logic

universes u v
/- Note to self: Figure out how to make this extensible
- i.e. I don't want to have to write:
- + Two TCs
- + Two instances
- + and a notation declaration
- EVERY SINGLE TIME!
-/

/-- Can perform a lifting operation `↑a`. -/
class has_lift (a : Sort u) (b : Sort v) :=
(lift : a → b)

/-- Auxiliary class that contains the transitive closure of `has_lift`. -/
class has_lift_t (a : Sort u) (b : Sort v) :=
(lift : a → b)

/-!
We specify the universes in `has_coe`, `has_coe_to_fun`, and `has_coe_to_sort`
explicitly in order to match exactly what appears in Lean4.
-/

class has_coe (a : Sort u) (b : Sort v) : Sort (max (max 1 u) v) :=
(coe : a → b)

/-- Auxiliary class that contains the transitive closure of `has_coe`. -/
class has_coe_t (a : Sort u) (b : Sort v) :=
(coe : a → b)

class has_coe_to_fun (a : Sort u) (F : out_param (a → Sort v)) :
  Sort (max (max 1 u) v) :=
(coe : Π x, F x)

class has_coe_to_sort (a : Sort u) (S : out_param (Sort v)) :
  Sort (max (max 1 u) v) :=
(coe : a → S)

def lift {a : Sort u} {b : Sort v} [has_lift a b] : a → b :=
@has_lift.lift a b _

def lift_t {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
@has_lift_t.lift a b _

def coe_b {a : Sort u} {b : Sort v} [has_coe a b] : a → b :=
@has_coe.coe a b _

def coe_t {a : Sort u} {b : Sort v} [has_coe_t a b] : a → b :=
@has_coe_t.coe a b _

def coe_fn_b {a : Sort u} {b : a → Sort v} [has_coe_to_fun a b] :
  Π x : a, b x :=
has_coe_to_fun.coe

/-! ### User level coercion operators -/

@[reducible] def coe {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
lift_t

@[reducible] def coe_fn {a : Sort u} {b : a → Sort v} [has_coe_to_fun a b] :
  Π x : a, b x :=
has_coe_to_fun.coe

@[reducible] def coe_sort {a : Sort u} {b : Sort v} [has_coe_to_sort a b] : a → b :=
has_coe_to_sort.coe

universes u₁ u₂ u₃

/-! ### Transitive closure for `has_lift`, `has_coe`, `has_coe_to_fun` -/

instance lift_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_lift_t b c] [has_lift a b] : has_lift_t a c :=
⟨λ x, lift_t (lift x : b)⟩

instance lift_base {a : Sort u} {b : Sort v} [has_lift a b] : has_lift_t a b :=
⟨lift⟩

instance coe_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe_t b c] [has_coe a b] : has_coe_t a c :=
⟨λ x, coe_t (coe_b x : b)⟩

instance coe_base {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t a b :=
⟨coe_b⟩

/-- We add this instance directly into `has_coe_t` to avoid non-termination.
   Suppose coe_option had type `(has_coe a (option a))`.
   Then, we can loop when searching a coercion from `α` to `β` `(has_coe_t α β)`
   1. `coe_trans at (has_coe_t α β)`
          `(has_coe α ?b₁) and (has_coe_t ?b₁ c)`
   2. `coe_option at (has_coe α ?b₁)`
          `?b₁ := option α`
   3. `coe_trans at (has_coe_t (option α) β)`
          `(has_coe (option α) ?b₂) and (has_coe_t ?b₂ β)`
   4. `coe_option at (has_coe (option α) ?b₂)`
          `?b₂ := option (option α))`
   ... -/
instance coe_option {a : Type u} : has_coe_t a (option a) :=
⟨λ x, some x⟩

/-- Auxiliary transitive closure for `has_coe` which does not contain
   instances such as `coe_option`.
   They would produce non-termination when combined with `coe_fn_trans` and `coe_sort_trans`. -/
class has_coe_t_aux (a : Sort u) (b : Sort v) :=
(coe : a → b)

instance coe_trans_aux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe_t_aux b c] [has_coe a b] :
  has_coe_t_aux a c :=
⟨λ x : a, @has_coe_t_aux.coe b c _ (coe_b x)⟩

instance coe_base_aux {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t_aux a b :=
⟨coe_b⟩

instance coe_fn_trans {a : Sort u₁} {b : Sort u₂} {c : b → Sort v} [has_coe_to_fun b c]
  [has_coe_t_aux a b] : has_coe_to_fun a (λ x, c (@has_coe_t_aux.coe a b _ x)) :=
⟨λ x, coe_fn (@has_coe_t_aux.coe a b _ x)⟩

instance coe_sort_trans {a : Sort u₁} {b : Sort u₂} {c : Sort v} [has_coe_to_sort b c] [has_coe_t_aux a b] :
  has_coe_to_sort a c :=
⟨λ x, coe_sort (@has_coe_t_aux.coe a b _ x)⟩

/-- Every coercion is also a lift -/
instance coe_to_lift {a : Sort u} {b : Sort v} [has_coe_t a b] : has_lift_t a b :=
⟨coe_t⟩