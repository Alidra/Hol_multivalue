Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1145802 : forall {_26945 : Type'}, forall x : _26945, forall l1 : list _26945, forall l2 : list _26945, (@List.In _26945 x (@List.app _26945 l1 l2)) = ((@List.In _26945 x l1) \/ (@List.In _26945 x l2)).
