Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9127 : forall {A B : Type'} (t : A -> B), (fun x : A => t x) = t.
