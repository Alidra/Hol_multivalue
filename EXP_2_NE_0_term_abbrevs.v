Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term15 (x0 : nat) := Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term1 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term9 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term4 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term19 := and ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term20 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term25 := forall y0 : nat, ~ ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) = (NUMERAL 0)).
Definition term14 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term3 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term23 := fun y0 : nat => ~ ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) = (NUMERAL 0)).
Definition term5 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term7 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term26 := forall y0 : nat, True.
Definition term24 := fun y0 : nat => True.
Definition term17 := NUMERAL (BIT0 (BIT1 0)).
Definition term22 (x0 : nat) := ~ ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) = (NUMERAL 0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term18 := BIT0 (BIT1 0).
Definition term28 (x0 : Prop) := forall y0 : nat, x0.
Definition term2 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term21 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term16 (x0 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))).
Definition term12 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
