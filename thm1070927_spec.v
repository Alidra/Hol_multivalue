Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070927 : forall {A : Type'} (list' : (recspace A) -> Prop) (NIL' : recspace A) (CONS' : A -> (recspace A) -> recspace A) (h1 : list' = (fun a : recspace A => forall list'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = NIL') \/ (exists a0 : A, exists a1 : recspace A, (a' = (CONS' a0 a1)) /\ (list'' a1))) -> list'' a') -> list'' a)), (list' NIL') /\ (forall a0 : A, forall a1 : recspace A, (list' a1) -> list' (CONS' a0 a1)).
