Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1804 : forall {_739 : Type'} (x : _739) (p : Prop), True = (((x = x) -> p) = p).
