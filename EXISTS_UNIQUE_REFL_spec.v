Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4476 : forall {A : Type'}, forall a : A, @ex1 A (fun x : A => x = a).
