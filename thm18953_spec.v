Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18953 : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), ((fun Q' : A -> Prop => (forall x : A, (P x) /\ (Q' x)) = ((forall x : A, P x) /\ (forall x : A, Q' x))) Q) = ((forall x : A, (P x) /\ (Q x)) = ((forall x : A, P x) /\ (forall x : A, Q x))).
