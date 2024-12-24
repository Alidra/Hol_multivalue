Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0)) x0.
Definition term1 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term36 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term33 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 y0) = (@nsum a0 y0 (fun y1 : a0 => NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@CARD a0 x0).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = True.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := ((@FINITE a0 x0) -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = True) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = ((@FINITE a0 x0) -> True).
Definition term7 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0))).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((@FINITE a0 x0) = (@FINITE a0 x0)) -> ((@FINITE a0 x0) -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = x1) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = ((@FINITE a0 x0) -> x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0))) = (Nat.mul (@CARD a0 x0) (NUMERAL (BIT1 0))).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((@FINITE a0 x0) = x1) -> (x1 -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y1 : a0 => NUMERAL (BIT1 0)))) = y0) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y1 : a0 => NUMERAL (BIT1 0)))) = (x1 -> y0)) x2.
Definition term3 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term8 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((@FINITE a0 x0) -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = x1) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = ((@FINITE a0 x0) -> x1).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : Prop, ((@FINITE a0 x0) = x1) -> (x1 -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y1 : a0 => NUMERAL (BIT1 0)))) = y0) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y1 : a0 => NUMERAL (BIT1 0)))) = (x1 -> y0).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term32 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@FINITE a0 x0) = y0) -> (y0 -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y2 : a0 => NUMERAL (BIT1 0)))) = y1) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y2 : a0 => NUMERAL (BIT1 0)))) = (y0 -> y1).
Definition term14 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term2 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term5 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := Nat.mul (@CARD a0 x0) (NUMERAL (BIT1 0)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @nsum a0 x0 (fun y0 : a0 => x1).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@FINITE a0 x0) = y0) -> (y0 -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y2 : a0 => NUMERAL (BIT1 0)))) = y1) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y2 : a0 => NUMERAL (BIT1 0)))) = (y0 -> y1)) x1.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : Prop) := ((@FINITE a0 x0) = x1) -> (x1 -> ((@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = x2) -> ((@FINITE a0 x0) -> (@CARD a0 x0) = (@nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)))) = (x1 -> x2).
Definition term31 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 y0) = (@nsum a0 y0 (fun y1 : a0 => NUMERAL (BIT1 0))).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> True.
Definition term0 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term24 := NUMERAL (BIT1 0).
Definition term34 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := @nsum a0 x0 (fun y0 : a0 => NUMERAL (BIT1 0)).
