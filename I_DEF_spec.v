Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15398 : forall {A : Type'}, (@I A) = (fun x : A => x).
