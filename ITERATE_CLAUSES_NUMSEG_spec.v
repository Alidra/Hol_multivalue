Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6192133 : forall {_123419 : Type'} (f : nat -> _123419), forall op : _123419 -> _123419 -> _123419, (@monoidal _123419 op) -> (forall m : nat, (@iterate _123419 nat op (dotdot m (NUMERAL 0)) f) = (@COND _123419 (m = (NUMERAL 0)) (f (NUMERAL 0)) (@neutral _123419 op))) /\ (forall m : nat, forall n : nat, (@iterate _123419 nat op (dotdot m (S n)) f) = (@COND _123419 (Peano.le m (S n)) (op (@iterate _123419 nat op (dotdot m n) f) (f (S n))) (@iterate _123419 nat op (dotdot m n) f))).
