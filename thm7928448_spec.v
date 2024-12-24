Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7928448 : forall {A : Type'} (a : finite_sum (finite_sum A A) unit), (fun a' : recspace (finite_sum (finite_sum A A) unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a'' : recspace (finite_sum (finite_sum A A) unit), (exists a''' : finite_sum (finite_sum A A) unit, a'' = ((fun a'''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a'''' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a''')) -> tybit1' a'') -> tybit1' a') ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a).
