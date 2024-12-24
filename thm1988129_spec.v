Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1988129 : forall {A : Type'} (P : Prop) (Q : A -> Prop), ((fun Q' : A -> Prop => (P /\ (exists x : A, Q' x)) = (exists x : A, P /\ (Q' x))) Q) = ((P /\ (exists x : A, Q x)) = (exists x : A, P /\ (Q x))).
