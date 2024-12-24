Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1862 : forall {A : Type'} (x : A), (fun x' : A => (x' = x') = True) x.
