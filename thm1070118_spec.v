Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070118 : forall {A : Type'} (a : A) (SOME' : A -> recspace A) (h1 : SOME' = (fun a' : A => @CONSTR A (S (NUMERAL 0)) a' (fun n : nat => @BOTTOM A))), (@Some A a) = (@_mk_option A (SOME' a)).
