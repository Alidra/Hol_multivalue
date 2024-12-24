Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48019 : forall {A B : Type'}, forall x : A, forall y : B, (@snd A B (@pair A B x y)) = y.
