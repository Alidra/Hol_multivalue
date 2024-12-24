Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7068649 : forall {_131679 : Type'}, forall f : _131679 -> real, forall s : _131679 -> Prop, (@sum _131679 (@support _131679 real real_add f s) f) = (@sum _131679 s f).
