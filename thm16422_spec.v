Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16422 : forall {A : Type'} (P : Prop) (Q : A -> Prop), ((fun Q' : A -> Prop => (forall x : A, P \/ (Q' x)) = (P \/ (forall x : A, Q' x))) Q) = ((forall x : A, P \/ (Q x)) = (P \/ (forall x : A, Q x))).
