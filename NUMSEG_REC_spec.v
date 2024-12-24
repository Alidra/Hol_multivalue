Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5371143 : forall m : nat, forall n : nat, (Peano.le m (S n)) -> (dotdot m (S n)) = (@INSERT nat (S n) (dotdot m n)).
