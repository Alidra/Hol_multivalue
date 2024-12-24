Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7925129 : forall {A : Type'} (a : finite_sum A A), (fun a' : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a'' : recspace (finite_sum A A), (exists a''' : finite_sum A A, a'' = ((fun a'''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a'''' (fun n : nat => @BOTTOM (finite_sum A A))) a''')) -> tybit0' a'') -> tybit0' a') ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a' (fun n : nat => @BOTTOM (finite_sum A A))) a).
