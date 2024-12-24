Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069014 : forall {A B : Type'} (y : B), (@OUTR A B (@inr A B y)) = y.
