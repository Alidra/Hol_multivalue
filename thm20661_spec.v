Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20661 : forall {A B : Type'} (f : A -> B) (x : A), (fun x' : A => (f x') = (@I (A -> B) f x')) x.
