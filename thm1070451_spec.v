Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070451 : forall {A : Type'} (CONS' : A -> (recspace A) -> recspace A) (h1 : CONS' = (fun a0 : A => fun a1 : recspace A => @CONSTR A (S (NUMERAL 0)) a0 (@FCONS (recspace A) a1 (fun n : nat => @BOTTOM A)))), CONS' = (fun a0 : A => fun a1 : recspace A => @CONSTR A (S (NUMERAL 0)) a0 (@FCONS (recspace A) a1 (fun n : nat => @BOTTOM A))).
