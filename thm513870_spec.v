Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513870 : ((forall m : nat, forall n : nat, (Nat.add m n) = (Nat.add m n)) /\ ((0 = 0) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n)))))))))))) = ((forall m : nat, forall n : nat, (Nat.add (NUMERAL m) (NUMERAL n)) = (NUMERAL (Nat.add m n))) /\ (((Nat.add 0 0) = 0) /\ ((forall n : nat, (Nat.add 0 (BIT0 n)) = (BIT0 n)) /\ ((forall n : nat, (Nat.add 0 (BIT1 n)) = (BIT1 n)) /\ ((forall n : nat, (Nat.add (BIT0 n) 0) = (BIT0 n)) /\ ((forall n : nat, (Nat.add (BIT1 n) 0) = (BIT1 n)) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT0 m) (BIT0 n)) = (BIT0 (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT0 m) (BIT1 n)) = (BIT1 (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT0 n)) = (BIT1 (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT1 n)) = (BIT0 (S (Nat.add m n))))))))))))).