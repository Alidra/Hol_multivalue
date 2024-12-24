Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem52 : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
