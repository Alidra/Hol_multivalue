Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9233 : forall {A B : Type'} (t : A -> B), ((fun t' : A -> B => t' = (fun x : A => t' x)) t) = (t = (fun x : A => t x)).
