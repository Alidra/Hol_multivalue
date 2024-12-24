Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3306861 : forall {A : Type'}, forall x : A, (@DELETE A (@EMPTY A) x) = (@EMPTY A).
