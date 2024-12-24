Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1071333 : forall {A : Type'} (NIL' : recspace A) (h1 : NIL' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))), (@nil A) = (@_mk_list A NIL').
