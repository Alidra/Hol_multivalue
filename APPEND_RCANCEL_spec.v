Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1188381 : forall {A : Type'}, forall l1 : list A, forall l2 : list A, forall l3 : list A, ((@List.app A l1 l3) = (@List.app A l2 l3)) = (l1 = l2).
