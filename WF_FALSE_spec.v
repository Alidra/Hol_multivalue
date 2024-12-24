Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem369125 : forall {A : Type'}, @WF A (fun x : A => fun y : A => False).
