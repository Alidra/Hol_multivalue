Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073632 : forall {A : Type'}, forall a0 : A, forall a1 : list A, forall a0' : A, forall a1' : list A, ((@cons A a0 a1) = (@cons A a0' a1')) = ((a0 = a0') /\ (a1 = a1')).
