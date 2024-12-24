Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (NUMERAL x0) (NUMERAL x1)).
Definition term1 (x0 : nat) := Nat.pow (NUMERAL x0).
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term17 := True /\ (((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))))).
Definition term13 := forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1)).
Definition term16 := (forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))) /\ (((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1)))))))))))).
Definition term9 := forall y0 : nat, True.
Definition term15 := ((Nat.pow 0 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT0 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow (BIT1 y0) 0) = (BIT1 0)) /\ ((forall y0 : nat, (Nat.pow 0 (BIT0 y0)) = (Nat.mul (Nat.pow 0 y0) (Nat.pow 0 y0))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT0 y1)) = (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))) /\ ((forall y0 : nat, (Nat.pow 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.pow (BIT0 y0) (BIT1 y1)) = (Nat.mul (BIT0 y0) (Nat.mul (Nat.pow (BIT0 y0) y1) (Nat.pow (BIT0 y0) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow (BIT1 y0) (BIT1 y1)) = (Nat.mul (BIT1 y0) (Nat.mul (Nat.pow (BIT1 y0) y1) (Nat.pow (BIT1 y0) y1))))))))))).
Definition term7 := fun y0 : nat => True.
Definition term4 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term14 := and (forall y0 : nat, forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1))).
Definition term6 (x0 : nat) := fun y0 : nat => (Nat.pow (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.pow x0 y0)).
Definition term5 (x0 : nat) (x1 : nat) := NUMERAL (Nat.pow x0 x1).
Definition term11 (x0 : Prop) := forall y0 : nat, x0.
Definition term2 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL x0) (NUMERAL x1).
Definition term12 := fun y0 : nat => forall y1 : nat, (Nat.pow (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.pow y0 y1)).
