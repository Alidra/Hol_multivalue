Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7221508 : forall f : nat -> real, forall m : nat, forall n : nat, ((forall p : nat, ((Peano.le m p) /\ (Peano.le p n)) -> real_le (real_of_num (NUMERAL 0)) (f p)) /\ ((@sum nat (dotdot m n) f) = (real_of_num (NUMERAL 0)))) -> forall p : nat, ((Peano.le m p) /\ (Peano.le p n)) -> (f p) = (real_of_num (NUMERAL 0)).
