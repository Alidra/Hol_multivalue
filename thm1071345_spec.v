Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1071345 : forall {A : Type'} (CONS' : A -> (recspace A) -> recspace A) (h1 : CONS' = (fun a0 : A => fun a1 : recspace A => @CONSTR A (S (NUMERAL 0)) a0 (@FCONS (recspace A) a1 (fun n : nat => @BOTTOM A)))), (fun a0 : A => fun a1 : list A => @_mk_list A (CONS' a0 (@_dest_list A a1))) = (fun a0 : A => fun a1 : list A => @_mk_list A ((fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a0 (@_dest_list A a1))).
