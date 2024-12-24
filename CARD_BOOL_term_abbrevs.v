Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : Prop -> Prop) (x1 : nat) := ~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)).
Definition term115 := (~ False) -> False.
Definition term7 (a0 : Type') := (((~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term47 (x0 : Prop -> Prop) := forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term49 (x0 : Prop -> Prop) := fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0))).
Definition term107 (x0 : Prop) := ~ (~ x0).
Definition term55 (x0 : Prop -> Prop) := fun y0 : nat => ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term60 (x0 : Prop -> Prop) := forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0))).
Definition term10 := ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term97 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1))) x0.
Definition term77 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) x0.
Definition term75 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0.
Definition term48 (x0 : Prop -> Prop) := (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term94 (x0 : Prop -> Prop) := forall y0 : nat, ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0)).
Definition term92 (x0 : Prop -> Prop) (x1 : nat) := ~ (@HAS_SIZE Prop x0 x1).
Definition term113 := (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))).
Definition term9 := (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term38 (x0 : Prop -> Prop) (x1 : nat) := ((@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)))) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term64 (x0 : Prop -> Prop) := forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0.
Definition term59 (x0 : Prop -> Prop) := forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0.
Definition term105 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term106 (x0 : Prop -> Prop) (x1 : nat) := (~ (~ (@HAS_SIZE Prop x0 x1))) -> (@CARD Prop x0) = x1.
Definition term45 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term39 (x0 : Prop -> Prop) := fun y0 : nat => ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term15 (a0 : Type') := imp (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term12 := imp (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term101 (x0 : Prop) := (~ x0) -> x0.
Definition term36 (x0 : Prop -> Prop) (x1 : nat) := and ((@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)))).
Definition term108 (x0 : Prop -> Prop) (x1 : nat) := ~ (~ (@HAS_SIZE Prop x0 x1)).
Definition term88 := forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0.
Definition term83 := forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0.
Definition term16 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term57 (x0 : Prop -> Prop) := @eq Prop (forall y0 : nat, ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)))).
Definition term56 (x0 : Prop -> Prop) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0)).
Definition term78 (x0 : Prop -> Prop) := ((fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0) /\ ((fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) x0).
Definition term98 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0))) x1.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term3 := ~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term91 (x0 : Prop -> Prop) (x1 : nat) := ((~ (@HAS_SIZE Prop x0 x1)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@CARD Prop x0) = x1)).
Definition term90 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y0 : Prop -> Prop, forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term5 (a0 : Type') := (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term11 := @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term19 (a0 : Type') := (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term8 (a0 : Type') := (((~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> ((~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term62 (x0 : Prop -> Prop) := and (forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))).
Definition term69 (x0 : type920) (x1 : type920) := forall y0 : Prop -> Prop, (x0 y0) /\ (x1 y0).
Definition term17 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term86 := and (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))).
Definition term53 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))) x1.
Definition term63 (x0 : Prop -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0.
Definition term58 (x0 : Prop -> Prop) := fun y0 : nat => (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0.
Definition term51 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1.
Definition term76 (x0 : Prop -> Prop) := and ((fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0).
Definition term13 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term102 (x0 : Prop -> Prop) (x1 : nat) := ((@CARD Prop x0) = x1) \/ (~ (@HAS_SIZE Prop x0 x1)).
Definition term110 (x0 : Prop -> Prop) (x1 : nat) := imp (@HAS_SIZE Prop x0 x1).
Definition term99 (x0 : Prop -> Prop) (x1 : nat) := (~ (@HAS_SIZE Prop x0 x1)) \/ ((@CARD Prop x0) = x1).
Definition term32 (x0 : Prop -> Prop) (x1 : nat) := or (@HAS_SIZE Prop x0 x1).
Definition term80 := @eq Prop (forall y0 : Prop -> Prop, ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0)).
Definition term67 := fun y0 : Prop -> Prop => (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term14 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term35 (x0 : Prop -> Prop) (x1 : nat) := and ((@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)))).
Definition term54 (x0 : Prop -> Prop) (x1 : nat) := ((fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1) /\ ((fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))) x1).
Definition term46 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term20 (x0 : Prop -> Prop) (x1 : nat) := (@FINITE Prop x0) /\ ((@CARD Prop x0) = x1).
Definition term112 := (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> (@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))).
Definition term1 := NUMERAL (BIT0 (BIT1 0)).
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term6 (a0 : Type') := ((~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term66 (x0 : Prop -> Prop) := (forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ (forall y0 : nat, (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term34 (x0 : Prop -> Prop) (x1 : nat) := (@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1))).
Definition term96 := forall y0 : Prop -> Prop, forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1)).
Definition term89 := forall y0 : Prop -> Prop, forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term84 := forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1))).
Definition term42 := forall y0 : Prop -> Prop, forall y1 : nat, ((@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term4 := forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term65 (x0 : Prop -> Prop) := forall y0 : nat, (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term103 (x0 : Prop -> Prop) (x1 : nat) := @eq Prop ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@CARD Prop x0) = x1)).
Definition term2 := (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term30 (x0 : Prop -> Prop) (x1 : nat) := (~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)).
Definition term114 := ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term95 := fun y0 : Prop -> Prop => forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1)).
Definition term74 := fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term73 := fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1))).
Definition term41 := fun y0 : Prop -> Prop => forall y1 : nat, ((@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term23 := fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term100 := (~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))))) -> @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term22 (x0 : Prop -> Prop) := forall y0 : nat, (@HAS_SIZE Prop x0 y0) = ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term72 := (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term87 := fun y0 : Prop -> Prop => (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0.
Definition term82 := fun y0 : Prop -> Prop => (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0.
Definition term18 := imp (~ ((@CARD Prop (@UNIV Prop)) = (NUMERAL (BIT0 (BIT1 0))))).
Definition term79 := fun y0 : Prop -> Prop => ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term50 (x0 : Prop -> Prop) := fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term61 (x0 : Prop -> Prop) := and (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0).
Definition term37 (x0 : Prop -> Prop) (x1 : nat) := ((@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)))) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term21 (x0 : Prop -> Prop) := fun y0 : nat => (@HAS_SIZE Prop x0 y0) = ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term85 := and (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term33 (x0 : Prop -> Prop) (x1 : nat) := (@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term52 (x0 : Prop -> Prop) (x1 : nat) := and ((fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1).
Definition term81 := @eq Prop (forall y0 : Prop -> Prop, (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)))).
Definition term27 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term104 (x0 : Prop -> Prop) (x1 : nat) := @eq Prop (((@CARD Prop x0) = x1) \/ (~ (@HAS_SIZE Prop x0 x1))).
Definition term93 (x0 : Prop -> Prop) := fun y0 : nat => ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0)).
Definition term71 := forall y0 : Prop -> Prop, ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term31 (x0 : Prop -> Prop) (x1 : nat) := (~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)).
Definition term70 (x0 : type920) (x1 : type920) := (forall y0 : Prop -> Prop, x0 y0) /\ (forall y0 : Prop -> Prop, x1 y0).
Definition term68 := forall y0 : Prop -> Prop, (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term40 (x0 : Prop -> Prop) := forall y0 : nat, ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term111 (x0 : Prop -> Prop) (x1 : nat) := (@HAS_SIZE Prop x0 x1) -> (@CARD Prop x0) = x1.
Definition term109 (x0 : Prop -> Prop) (x1 : nat) := imp (~ (~ (@HAS_SIZE Prop x0 x1))).
