Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7216412 : forall m : nat, forall n : nat, forall f : nat -> real, (forall p : nat, ((Peano.le m p) /\ (Peano.le p n)) -> real_le (real_of_num (NUMERAL 0)) (f p)) -> real_le (real_of_num (NUMERAL 0)) (@sum nat (dotdot m n) f).
