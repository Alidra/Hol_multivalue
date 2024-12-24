Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7930003 : forall {A Z : Type'}, forall _103802' : (finite_sum (finite_sum A A) unit) -> Z, exists fn : (tybit1 A) -> Z, forall a : finite_sum (finite_sum A A) unit, (fn (@_103802 A a)) = (_103802' a).
