Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1116330 : forall {A : Type'}, forall l1 : list A, forall l2 : list A, (l1 = l2) = (((@List.length A l1) = (@List.length A l2)) /\ (forall n : nat, (Peano.lt n (@List.length A l2)) -> (@EL A n l1) = (@EL A n l2))).
