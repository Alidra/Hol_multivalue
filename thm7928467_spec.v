Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7928467 : forall {A : Type'} (_103802' : (finite_sum (finite_sum A A) unit) -> recspace (finite_sum (finite_sum A A) unit)) (h1 : _103802' = (fun a : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit)))), (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A (_103802' a)) = (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a)).
