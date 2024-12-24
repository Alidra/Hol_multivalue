Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3185620 : forall {A : Type'}, (fun x : A => False) = (fun x : A => False).
