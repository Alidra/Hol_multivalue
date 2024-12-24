Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1206267 : forall {_28249 : Type'}, forall n : nat, forall h : _28249, forall t : list _28249, (@EL _28249 n (@cons _28249 h t)) = (@COND _28249 (n = (NUMERAL 0)) h (@EL _28249 (Nat.sub n (NUMERAL (BIT1 0))) t)).
