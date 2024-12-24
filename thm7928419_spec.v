Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7928419 : forall {A : Type'} (tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop) (_103802' : (finite_sum (finite_sum A A) unit) -> recspace (finite_sum (finite_sum A A) unit)) (h1 : tybit1' = (fun a : recspace (finite_sum (finite_sum A A) unit) => forall tybit1'' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) unit), (exists a'' : finite_sum (finite_sum A A) unit, a' = (_103802' a'')) -> tybit1'' a') -> tybit1'' a)), forall a : finite_sum (finite_sum A A) unit, tybit1' (_103802' a).
