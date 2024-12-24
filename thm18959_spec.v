Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18959 : forall {A : Type'} (P : Prop) (Q : A -> Prop), ((fun Q' : A -> Prop => (exists x : A, P /\ (Q' x)) = (P /\ (exists x : A, Q' x))) Q) = ((exists x : A, P /\ (Q x)) = (P /\ (exists x : A, Q x))).
