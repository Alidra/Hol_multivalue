Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9524 : forall {A : Type'} (x : A), ((fun x' : A => (@ε A (fun y : A => y = x')) = x') x) = ((@ε A (fun y : A => y = x)) = x).
