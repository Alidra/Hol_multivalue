Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem57692 : forall {A B : Type'} (f : A -> B) (x : A), ((fun x' : A => (@LET A B f x') = (f x')) x) = ((@LET A B f x) = (f x)).
