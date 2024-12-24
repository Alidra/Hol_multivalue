Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem520357 : (forall m : nat, forall n : nat, (Peano.lt (NUMERAL m) (NUMERAL n)) = (Peano.lt m n)) /\ (((Peano.lt 0 0) = False) /\ ((forall n : nat, (Peano.lt (BIT0 n) 0) = False) /\ ((forall n : nat, (Peano.lt (BIT1 n) 0) = False) /\ ((forall n : nat, (Peano.lt 0 (BIT0 n)) = (Peano.lt 0 n)) /\ ((forall n : nat, (Peano.lt 0 (BIT1 n)) = True) /\ ((forall m : nat, forall n : nat, (Peano.lt (BIT0 m) (BIT0 n)) = (Peano.lt m n)) /\ ((forall m : nat, forall n : nat, (Peano.lt (BIT0 m) (BIT1 n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (Peano.lt (BIT1 m) (BIT0 n)) = (Peano.lt m n)) /\ (forall m : nat, forall n : nat, (Peano.lt (BIT1 m) (BIT1 n)) = (Peano.lt m n)))))))))).
