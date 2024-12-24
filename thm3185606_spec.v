Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3185606 : forall {A : Type'}, (@EMPTY A) = (fun x : A => False).
