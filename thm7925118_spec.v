Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7925118 : forall {A : Type'} (tybit0' : (recspace (finite_sum A A)) -> Prop) (_103783' : (finite_sum A A) -> recspace (finite_sum A A)) (h1 : _103783' = (fun a : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a (fun n : nat => @BOTTOM (finite_sum A A)))) (h2 : tybit0' = (fun a : recspace (finite_sum A A) => forall tybit0'' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = (_103783' a'')) -> tybit0'' a') -> tybit0'' a)), tybit0' = (fun a : recspace (finite_sum A A) => forall tybit0'' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a''' (fun n : nat => @BOTTOM (finite_sum A A))) a'')) -> tybit0'' a') -> tybit0'' a).
