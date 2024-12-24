Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105738 : forall {_25569 : Type'}, (forall l : list _25569, (@EL _25569 (NUMERAL 0) l) = (@hd _25569 l)) /\ (forall n : nat, forall l : list _25569, (@EL _25569 (S n) l) = (@EL _25569 n (@tl _25569 l))).
