Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7925148 : forall {A : Type'} (_103783' : (finite_sum A A) -> recspace (finite_sum A A)) (h1 : _103783' = (fun a : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a (fun n : nat => @BOTTOM (finite_sum A A)))), (fun a : finite_sum A A => @_mk_tybit0 A (_103783' a)) = (fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a' (fun n : nat => @BOTTOM (finite_sum A A))) a)).
