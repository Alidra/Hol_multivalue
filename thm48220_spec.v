Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48220 : forall {A B : Type'} (y : B) (x : A), ((fun y' : B => (@fst A B (@pair A B x y')) = x) y) = ((@fst A B (@pair A B x y)) = x).
