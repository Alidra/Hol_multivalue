Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem519780 : (forall m : nat, forall n : nat, (Peano.le (NUMERAL m) (NUMERAL n)) = (Peano.le m n)) /\ (((Peano.le 0 0) = True) /\ ((forall n : nat, (Peano.le (BIT0 n) 0) = (Peano.le n 0)) /\ ((forall n : nat, (Peano.le (BIT1 n) 0) = False) /\ ((forall n : nat, (Peano.le 0 (BIT0 n)) = True) /\ ((forall n : nat, (Peano.le 0 (BIT1 n)) = True) /\ ((forall m : nat, forall n : nat, (Peano.le (BIT0 m) (BIT0 n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (Peano.le (BIT0 m) (BIT1 n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (Peano.le (BIT1 m) (BIT0 n)) = (Peano.lt m n)) /\ (forall m : nat, forall n : nat, (Peano.le (BIT1 m) (BIT1 n)) = (Peano.le m n)))))))))).
