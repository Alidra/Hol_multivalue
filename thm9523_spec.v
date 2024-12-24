Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9523 : forall {A : Type'} (x : A), (fun x' : A => (@ε A (fun y : A => y = x')) = x') x.
