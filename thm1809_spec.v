Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1809 : forall {A B : Type'} (f : A -> B) (y : A), (fun y' : A => ((fun x : A => f x) y') = (f y')) y.
