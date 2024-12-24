Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : Prop -> Prop) (x1 : nat) := ~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)).
Definition term107 := (~ False) -> False.
Definition term6 := (((~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term38 (x0 : Prop -> Prop) := forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term40 (x0 : Prop -> Prop) := fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0))).
Definition term98 (x0 : Prop) := ~ (~ x0).
Definition term46 (x0 : Prop -> Prop) := fun y0 : nat => ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term105 := (~ (@FINITE Prop (@UNIV Prop))) -> @FINITE Prop (@UNIV Prop).
Definition term51 (x0 : Prop -> Prop) := forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0))).
Definition term9 := ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term88 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1))) x0.
Definition term68 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) x0.
Definition term66 (x0 : Prop -> Prop) := (fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0.
Definition term39 (x0 : Prop -> Prop) := (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0).
Definition term85 (x0 : Prop -> Prop) := forall y0 : nat, ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0)).
Definition term14 := imp (~ (@FINITE Prop (@UNIV Prop))).
Definition term83 (x0 : Prop -> Prop) (x1 : nat) := ~ (@HAS_SIZE Prop x0 x1).
Definition term8 := (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term29 (x0 : Prop -> Prop) (x1 : nat) := ((@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)))) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term55 (x0 : Prop -> Prop) := forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0.
Definition term50 (x0 : Prop -> Prop) := forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0.
Definition term96 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term36 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term30 (x0 : Prop -> Prop) := fun y0 : nat => ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term11 := imp (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term92 (x0 : Prop) := (~ x0) -> x0.
Definition term27 (x0 : Prop -> Prop) (x1 : nat) := and ((@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)))).
Definition term103 := (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> @FINITE Prop (@UNIV Prop).
Definition term90 (x0 : nat) (x1 : Prop -> Prop) := (~ (@HAS_SIZE Prop x1 x0)) \/ (@FINITE Prop x1).
Definition term99 (x0 : Prop -> Prop) (x1 : nat) := ~ (~ (@HAS_SIZE Prop x0 x1)).
Definition term79 := forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0.
Definition term74 := forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0.
Definition term97 (x0 : nat) (x1 : Prop -> Prop) := (~ (~ (@HAS_SIZE Prop x1 x0))) -> @FINITE Prop x1.
Definition term48 (x0 : Prop -> Prop) := @eq Prop (forall y0 : nat, ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)))).
Definition term47 (x0 : Prop -> Prop) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0)).
Definition term69 (x0 : Prop -> Prop) := ((fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0) /\ ((fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) x0).
Definition term89 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0))) x1.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term82 (x0 : Prop -> Prop) (x1 : nat) := ((~ (@HAS_SIZE Prop x0 x1)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@CARD Prop x0) = x1)).
Definition term81 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y0 : Prop -> Prop, forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term10 := @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term53 (x0 : Prop -> Prop) := and (forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))).
Definition term60 (x0 : type920) (x1 : type920) := forall y0 : Prop -> Prop, (x0 y0) /\ (x1 y0).
Definition term93 (x0 : Prop -> Prop) (x1 : nat) := (@FINITE Prop x0) \/ (~ (@HAS_SIZE Prop x0 x1)).
Definition term77 := and (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))).
Definition term44 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))) x1.
Definition term54 (x0 : Prop -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (@HAS_SIZE Prop x0 y1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y1))) y0.
Definition term49 (x0 : Prop -> Prop) := fun y0 : nat => (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0.
Definition term42 (x0 : Prop -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1.
Definition term67 (x0 : Prop -> Prop) := and ((fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) x0).
Definition term12 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term101 (x0 : Prop -> Prop) (x1 : nat) := imp (@HAS_SIZE Prop x0 x1).
Definition term23 (x0 : Prop -> Prop) (x1 : nat) := or (@HAS_SIZE Prop x0 x1).
Definition term95 (x0 : Prop -> Prop) (x1 : nat) := @eq Prop ((@FINITE Prop x0) \/ (~ (@HAS_SIZE Prop x0 x1))).
Definition term4 := (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term71 := @eq Prop (forall y0 : Prop -> Prop, ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0)).
Definition term58 := fun y0 : Prop -> Prop => (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term13 := (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term26 (x0 : Prop -> Prop) (x1 : nat) := and ((@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)))).
Definition term45 (x0 : Prop -> Prop) (x1 : nat) := ((fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1) /\ ((fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))) x1).
Definition term37 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term7 := (((~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> ((~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term16 (x0 : Prop -> Prop) (x1 : nat) := (@FINITE Prop x0) /\ ((@CARD Prop x0) = x1).
Definition term104 := NUMERAL (BIT0 (BIT1 0)).
Definition term15 := (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> ~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term57 (x0 : Prop -> Prop) := (forall y0 : nat, (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ (forall y0 : nat, (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term25 (x0 : Prop -> Prop) (x1 : nat) := (@HAS_SIZE Prop x0 x1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1))).
Definition term102 (x0 : nat) (x1 : Prop -> Prop) := (@HAS_SIZE Prop x1 x0) -> @FINITE Prop x1.
Definition term87 := forall y0 : Prop -> Prop, forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1)).
Definition term80 := forall y0 : Prop -> Prop, forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term75 := forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1))).
Definition term33 := forall y0 : Prop -> Prop, forall y1 : nat, ((@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term3 := forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term106 := (@FINITE Prop (@UNIV Prop)) -> False.
Definition term56 (x0 : Prop -> Prop) := forall y0 : nat, (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term21 (x0 : Prop -> Prop) (x1 : nat) := (~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = x1)).
Definition term86 := fun y0 : Prop -> Prop => forall y1 : nat, ((~ (@HAS_SIZE Prop y0 y1)) \/ (@FINITE Prop y0)) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@CARD Prop y0) = y1)).
Definition term65 := fun y0 : Prop -> Prop => forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term64 := fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1))).
Definition term32 := fun y0 : Prop -> Prop => forall y1 : nat, ((@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ ((~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term19 := fun y0 : Prop -> Prop => forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)).
Definition term91 := (~ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))))) -> @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term18 (x0 : Prop -> Prop) := forall y0 : nat, (@HAS_SIZE Prop x0 y0) = ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term63 := (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term2 := ~ (@FINITE Prop (@UNIV Prop)).
Definition term78 := fun y0 : Prop -> Prop => (fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0.
Definition term73 := fun y0 : Prop -> Prop => (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0.
Definition term70 := fun y0 : Prop -> Prop => ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term5 := ((~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False) -> (~ (@FINITE Prop (@UNIV Prop))) -> (forall y0 : Prop -> Prop, forall y1 : nat, (@HAS_SIZE Prop y0 y1) = ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))) -> (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))) -> False.
Definition term41 (x0 : Prop -> Prop) := fun y0 : nat => (~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term52 (x0 : Prop -> Prop) := and (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE Prop x0 y1) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y1)))) y0).
Definition term28 (x0 : Prop -> Prop) (x1 : nat) := ((@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)))) /\ ((~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term17 (x0 : Prop -> Prop) := fun y0 : nat => (@HAS_SIZE Prop x0 y0) = ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0)).
Definition term76 := and (forall y0 : Prop -> Prop, (fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term24 (x0 : Prop -> Prop) (x1 : nat) := (@HAS_SIZE Prop x0 x1) \/ (~ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1))).
Definition term43 (x0 : Prop -> Prop) (x1 : nat) := and ((fun y0 : nat => (@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) x1).
Definition term72 := @eq Prop (forall y0 : Prop -> Prop, (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1)))).
Definition term94 (x0 : nat) (x1 : Prop -> Prop) := @eq Prop ((~ (@HAS_SIZE Prop x1 x0)) \/ (@FINITE Prop x1)).
Definition term1 := (~ (@FINITE Prop (@UNIV Prop))) -> False.
Definition term84 (x0 : Prop -> Prop) := fun y0 : nat => ((~ (@HAS_SIZE Prop x0 y0)) \/ (@FINITE Prop x0)) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@CARD Prop x0) = y0)).
Definition term62 := forall y0 : Prop -> Prop, ((fun y1 : Prop -> Prop => forall y2 : nat, (@HAS_SIZE Prop y1 y2) \/ ((~ (@FINITE Prop y1)) \/ (~ ((@CARD Prop y1) = y2)))) y0) /\ ((fun y1 : Prop -> Prop => forall y2 : nat, (~ (@HAS_SIZE Prop y1 y2)) \/ ((@FINITE Prop y1) /\ ((@CARD Prop y1) = y2))) y0).
Definition term22 (x0 : Prop -> Prop) (x1 : nat) := (~ (@HAS_SIZE Prop x0 x1)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = x1)).
Definition term61 (x0 : type920) (x1 : type920) := (forall y0 : Prop -> Prop, x0 y0) /\ (forall y0 : Prop -> Prop, x1 y0).
Definition term59 := forall y0 : Prop -> Prop, (forall y1 : nat, (@HAS_SIZE Prop y0 y1) \/ ((~ (@FINITE Prop y0)) \/ (~ ((@CARD Prop y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE Prop y0 y1)) \/ ((@FINITE Prop y0) /\ ((@CARD Prop y0) = y1))).
Definition term31 (x0 : Prop -> Prop) := forall y0 : nat, ((@HAS_SIZE Prop x0 y0) \/ ((~ (@FINITE Prop x0)) \/ (~ ((@CARD Prop x0) = y0)))) /\ ((~ (@HAS_SIZE Prop x0 y0)) \/ ((@FINITE Prop x0) /\ ((@CARD Prop x0) = y0))).
Definition term100 (x0 : Prop -> Prop) (x1 : nat) := imp (~ (~ (@HAS_SIZE Prop x0 x1))).
