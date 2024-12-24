Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073843 : forall {A : Type'}, forall a : A, forall a' : A, ((@Some A a) = (@Some A a')) = (a = a').
