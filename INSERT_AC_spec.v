Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3291150 : forall {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop), ((@INSERT _86293 x (@INSERT _86293 y s)) = (@INSERT _86293 y (@INSERT _86293 x s))) /\ ((@INSERT _86293 x (@INSERT _86293 x s)) = (@INSERT _86293 x s)).
