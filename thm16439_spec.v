Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16439 : forall {A : Type'} (P : A -> Prop) (Q : Prop), (fun Q' : Prop => (exists x : A, (P x) /\ Q') = ((exists x : A, P x) /\ Q')) Q.