Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1342163 : forall y : real, forall x : real, (real_ge x y) = (real_le y x).