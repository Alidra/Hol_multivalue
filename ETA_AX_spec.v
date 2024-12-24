Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9121 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
