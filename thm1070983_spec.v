Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070983 : forall {A : Type'} (r : recspace A) (list' : (recspace A) -> Prop) (CONS' : A -> (recspace A) -> recspace A) (NIL' : recspace A) (h1 : CONS' = (fun a0 : A => fun a1 : recspace A => @CONSTR A (S (NUMERAL 0)) a0 (@FCONS (recspace A) a1 (fun n : nat => @BOTTOM A)))) (h2 : list' = (fun a : recspace A => forall list'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = NIL') \/ (exists a0 : A, exists a1 : recspace A, (a' = (CONS' a0 a1)) /\ (list'' a1))) -> list'' a') -> list'' a)) (h3 : NIL' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))), (list' r) = ((@_dest_list A (@_mk_list A r)) = r).
