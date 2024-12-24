Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069766 : forall {A : Type'} (NONE' : recspace A) (h1 : NONE' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))), (@None A) = (@_mk_option A NONE').
