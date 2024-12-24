Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4327265 : forall {A B : Type'}, forall x : A, forall y : B, (@CROSS B A (@INSERT A x (@EMPTY A)) (@INSERT B y (@EMPTY B))) = (@INSERT (prod A B) (@pair A B x y) (@EMPTY (prod A B))).
