Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5131560 : forall {_115095 _115098 : Type'}, forall s : _115098 -> Prop, forall t : _115095 -> Prop, (@ge_c _115095 _115098 s t) = (exists f : _115098 -> _115095, forall y : _115095, (@IN _115095 y t) -> exists x : _115098, (@IN _115098 x s) /\ (y = (f x))).
