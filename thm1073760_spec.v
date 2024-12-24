Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073760 : forall {A : Type'}, forall a' : A, ~ ((@None A) = (@Some A a')).
