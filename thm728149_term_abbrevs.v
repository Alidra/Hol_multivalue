Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := (forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))).
Definition term2 := (forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))).
Definition term1 := (forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))))))))).
Definition term0 := ((Nat.add 0 0) = 0) /\ ((forall y0 : nat, (Nat.add 0 (BIT0 y0)) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) /\ ((forall y0 : nat, (Nat.add (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))))))).
Definition term12 := S (BIT1 (BIT0 (BIT1 0))).
Definition term6 (x0 : nat) := (fun y0 : nat => (Nat.add (BIT1 y0) 0) = (BIT1 y0)) x0.
Definition term8 := Nat.add (BIT1 (BIT0 (BIT1 0))) 0.
Definition term7 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term5 := forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0).
Definition term10 := BIT0 (BIT1 0).
Definition term11 := S (Nat.add (BIT1 (BIT0 (BIT1 0))) 0).
Definition term4 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
Definition term9 := BIT1 (BIT0 (BIT1 0)).