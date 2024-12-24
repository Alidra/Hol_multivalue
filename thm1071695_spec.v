Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1071695 : forall {A : Type'} (a0 : A) (a1 : list A) (CONS' : A -> (recspace A) -> recspace A) (h1 : CONS' = (fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A)))), (@cons A a0 a1) = (@_mk_list A (CONS' a0 (@_dest_list A a1))).
