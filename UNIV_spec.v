Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3187417 : forall {A : Type'}, (@UNIV A) = (fun x : A => True).
