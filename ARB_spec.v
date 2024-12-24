Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4381730 : forall {A : Type'}, (@ARB A) = (@ε A (fun x : A => False)).
