Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1118281 : forall {_26221 : Type'}, forall l : list _26221, forall n : nat, ((@List.length _26221 l) = (S n)) = (exists h : _26221, exists t : list _26221, (l = (@cons _26221 h t)) /\ ((@List.length _26221 t) = n)).
