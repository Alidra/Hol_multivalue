Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16452 : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), ((fun Q' : A -> Prop => (exists x : A, (P x) \/ (Q' x)) = ((exists x : A, P x) \/ (exists x : A, Q' x))) Q) = ((exists x : A, (P x) \/ (Q x)) = ((exists x : A, P x) \/ (exists x : A, Q x))).
