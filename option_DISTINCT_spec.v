Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1074714 : forall {A : Type'}, forall a : A, ~ ((@Some A a) = (@None A)).
