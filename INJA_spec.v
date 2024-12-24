Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1055868 : forall {A : Type'}, forall a : A, (@INJA A a) = (fun n : nat => fun b : A => b = a).
