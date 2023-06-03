prelude

import .operations
import .core
import .logic
import .coe

noncomputable theory

set_option pp.beta true

universes u v w

def comp {α: Sort u} {β: Sort v} {γ: Sort w} (f: β → γ) (g: α → β): α → γ :=
  λx: α, f (g x)
instance fun_comp_fun(α: Sort u)(β: Sort v)(γ: Sort w):
  has_comp (β→γ)(α→β)(α→γ) := @has_comp.mk (β→γ)(α→β)(α→γ) (@comp α β γ)

constant T: Sort u
constant U: Sort v
constant V: Sort w 

constant f: U → V
constant g: T → U
constant h: U → U
#check h

-- WIll fix later, have another project in mind