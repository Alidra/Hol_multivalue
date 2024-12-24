Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5132744 : forall {_115106 : Type'}, forall t : _115106 -> Prop, (@COUNTABLE _115106 t) = (@ge_c _115106 nat (@UNIV nat) t).
