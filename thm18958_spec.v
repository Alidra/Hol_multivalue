Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18958 : forall {A : Type'} (P : Prop) (Q : A -> Prop), (fun Q' : A -> Prop => (exists x : A, P /\ (Q' x)) = (P /\ (exists x : A, Q' x))) Q.
