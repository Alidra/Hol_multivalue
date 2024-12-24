Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069016 : forall {A : Type'} (SOME' : A -> recspace A) (h1 : SOME' = (fun a : A => @CONSTR A (S (NUMERAL 0)) a (fun n : nat => @BOTTOM A))), SOME' = (fun a : A => @CONSTR A (S (NUMERAL 0)) a (fun n : nat => @BOTTOM A)).
