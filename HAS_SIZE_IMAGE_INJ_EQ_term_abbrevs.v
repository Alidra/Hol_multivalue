Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((~ y0) /\ (y0 -> x0 = x1)) -> ~ (y0 /\ x1)) x2.
Definition term44 (x0 : Prop) (x1 : Prop) := (False /\ (False -> x0 = x1)) -> x0 = (False /\ x1).
Definition term91 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := @eq Prop ((@FINITE a0 (@IMAGE a1 a0 x0 x1)) /\ ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2)).
Definition term62 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((~ x1) /\ (x1 -> x0 = x2)) -> ~ (x1 /\ x2).
Definition term89 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := (@FINITE a0 (@IMAGE a1 a0 x0 x1)) /\ ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2).
Definition term110 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := (@FINITE a1 x1) -> ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2) = ((@CARD a1 x1) = x2).
Definition term112 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := (forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x1) /\ ((@IN a1 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@HAS_SIZE a0 (@IMAGE a1 a0 x0 x1) x2) = (@HAS_SIZE a1 x1 x2).
Definition term29 (x0 : Prop) := and (True = x0).
Definition term104 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term115 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, forall y1 : a1 -> Prop, forall y2 : nat, (forall y3 : a1, forall y4 : a1, ((@IN a1 y3 y1) /\ ((@IN a1 y4 y1) /\ ((y0 y3) = (y0 y4)))) -> y3 = y4) -> (@HAS_SIZE a0 (@IMAGE a1 a0 y0 y1) y2) = (@HAS_SIZE a1 y1 y2).
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 = x2.
Definition term48 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term103 (a0 : Type') := forall y0 : a0, True.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@FINITE a1 (@IMAGE a0 a1 x0 y0)) = (@FINITE a0 y0).
Definition term105 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) := fun y0 : a1 => forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term97 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) := (fun y0 : a1 => forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1) x2.
Definition term96 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := ((forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x1) /\ ((@IN a1 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a1 x1)) -> (@CARD a0 (@IMAGE a1 a0 x0 x1)) = (@CARD a1 x1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a0 x1)) -> (@CARD a1 (@IMAGE a0 a1 x0 x1)) = (@CARD a0 x1).
Definition term17 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1).
Definition term8 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) /\ (@FINITE a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 y0 y1)) = (@CARD a0 y1)) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) /\ (@FINITE a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 y0 y1)) = (@CARD a0 y1).
Definition term54 (x0 : Prop) := and (False = x0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) /\ (@FINITE a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 y0 y1)) = (@CARD a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 x0 x1)) = (@CARD a0 x1).
Definition term70 (x0 : Prop) (x1 : Prop) := ((~ False) /\ (False -> x0 = x1)) -> ~ (False /\ x1).
Definition term108 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := @eq nat (@CARD a0 (@IMAGE a1 a0 x0 x1)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@CARD a0 x0).
Definition term61 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term63 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((~ y0) /\ (y0 -> x0 = x1)) -> ~ (y0 /\ x1).
Definition term31 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True = x0) /\ (x0 -> x1 = x2).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@FINITE a1 (@IMAGE a0 a1 x0 y0)) = (@FINITE a0 y0)) x1.
Definition term39 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (y0 -> x0 = x1)) -> x0 = (y0 /\ x1)) True.
Definition term78 (x0 : Prop) (x1 : Prop) := imp ((~ False) /\ (False -> x0 = x1)).
Definition term100 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : a1) := ((@IN a1 x2 x0) /\ ((@IN a1 x3 x0) /\ ((x1 x2) = (x1 x3)))) -> x2 = x3.
Definition term66 (x0 : Prop) (x1 : Prop) := ((~ True) /\ (True -> x0 = x1)) -> ~ (True /\ x1).
Definition term101 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) := fun y0 : a1 => ((@IN a1 x2 x0) /\ ((@IN a1 y0 x0) /\ ((x1 x2) = (x1 y0)))) -> x2 = y0.
Definition term37 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 /\ (y0 -> x0 = x1)) -> x0 = (y0 /\ x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) /\ (@FINITE a0 y0)) -> (@CARD a1 (@IMAGE a0 a1 x0 y0)) = (@CARD a0 y0)) x1.
Definition term80 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x1) /\ (x1 -> x2 = x3).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := @eq Prop (@HAS_SIZE a0 (@IMAGE a1 a0 x0 x1) x2).
Definition term32 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x0 -> x1 = x2).
Definition term88 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := @HAS_SIZE a0 (@IMAGE a1 a0 x0 x1) x2.
Definition term111 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := ((@FINITE a0 (@IMAGE a1 a0 x0 x1)) = (@FINITE a1 x1)) /\ ((@FINITE a1 x1) -> ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2) = ((@CARD a1 x1) = x2)).
Definition term59 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((~ x0) /\ (x0 -> x1 = x2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) /\ (@FINITE a0 y0)) -> (@CARD a1 (@IMAGE a0 a1 x0 y0)) = (@CARD a0 y0).
Definition term27 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x1 -> x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) False.
Definition term52 (x0 : Prop) (x1 : Prop) := imp (False /\ (False -> x0 = x1)).
Definition term34 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (x0 /\ (x0 -> x1 = x2)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term72 (x0 : Prop) (x1 : Prop) := (~ True) /\ (True -> x0 = x1).
Definition term45 (x0 : Prop) (x1 : Prop) := True /\ (True -> x0 = x1).
Definition term82 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 = x2) /\ (x2 -> x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)) -> ((x0 = x2) /\ (x2 -> x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term35 (x0 : Prop) := @eq Prop (True /\ x0).
Definition term102 (a0 : Type') := fun y0 : a0 => True.
Definition term71 := and (~ True).
Definition term49 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 = x1.
Definition term95 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := (forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x1) /\ ((@IN a1 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE a0 (@IMAGE a1 a0 x0 x1)) = (@FINITE a1 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = (@FINITE a0 x1).
Definition term50 (x0 : Prop) (x1 : Prop) := False /\ (False -> x0 = x1).
Definition term26 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop (((x0 = x2) /\ (x2 -> x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)).
Definition term81 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 = x2) /\ (x2 -> x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term68 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((~ x1) /\ (x1 -> x0 = x2)) -> ~ (x1 /\ x2)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term79 (x0 : Prop) := ~ (False /\ x0).
Definition term69 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) /\ (y0 -> x0 = x1)) -> ~ (y0 /\ x1)) False.
Definition term93 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := @FINITE a0 (@IMAGE a1 a0 x0 x1).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term57 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (~ x0) /\ (x0 -> x1 = x2).
Definition term56 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False = x0) /\ (x0 -> x1 = x2).
Definition term19 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term53 (x0 : Prop) := False -> ~ x0.
Definition term92 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : nat) := (((@FINITE a0 (@IMAGE a1 a0 x0 x1)) = (@FINITE a1 x1)) /\ ((@FINITE a1 x1) -> ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2) = ((@CARD a1 x1) = x2))) -> ((@FINITE a0 (@IMAGE a1 a0 x0 x1)) /\ ((@CARD a0 (@IMAGE a1 a0 x0 x1)) = x2)) = ((@FINITE a1 x1) /\ ((@CARD a1 x1) = x2)).
Definition term114 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a1 -> Prop, forall y1 : nat, (forall y2 : a1, forall y3 : a1, ((@IN a1 y2 y0) /\ ((@IN a1 y3 y0) /\ ((x0 y2) = (x0 y3)))) -> y2 = y3) -> (@HAS_SIZE a0 (@IMAGE a1 a0 x0 y0) y1) = (@HAS_SIZE a1 y0 y1).
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) /\ (@FINITE a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 y0 y1)) = (@CARD a0 y1).
Definition term60 (x0 : Prop) := @eq Prop (False /\ x0).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := @CARD a0 (@IMAGE a1 a0 x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @CARD a1 (@IMAGE a0 a1 x0 x1).
Definition term58 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((False = x0) /\ (x0 -> x1 = x2)).
Definition term33 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((True = x0) /\ (x0 -> x1 = x2)).
Definition term51 (x0 : Prop) (x1 : Prop) := False -> x0 = x1.
Definition term55 (x0 : Prop) := and (~ x0).
Definition term113 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := forall y0 : nat, (forall y1 : a1, forall y2 : a1, ((@IN a1 y1 x1) /\ ((@IN a1 y2 x1) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@HAS_SIZE a0 (@IMAGE a1 a0 x0 x1) y0) = (@HAS_SIZE a1 x1 y0).
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x0 = x2) /\ (x2 -> x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term107 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) := (forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x1) /\ ((@IN a1 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a1 x1).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@FINITE a0 x1).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 = x1) /\ (x1 -> x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) x3).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term46 (x0 : Prop) (x1 : Prop) := True -> x0 = x1.
Definition term87 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) := forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = (@FINITE a0 x1).
Definition term77 (x0 : Prop) (x1 : Prop) := (~ False) /\ (False -> x0 = x1).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => ((y0 = x1) /\ (x1 -> x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2).
Definition term40 (x0 : Prop) (x1 : Prop) := (True /\ (True -> x0 = x1)) -> x0 = (True /\ x1).
Definition term47 (x0 : Prop) (x1 : Prop) := imp (True /\ (True -> x0 = x1)).
Definition term98 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) := forall y0 : a1, ((@IN a1 x2 x0) /\ ((@IN a1 y0 x0) /\ ((x1 x2) = (x1 y0)))) -> x2 = y0.
Definition term65 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) /\ (y0 -> x0 = x1)) -> ~ (y0 /\ x1)) True.
Definition term76 := and (~ False).
Definition term106 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) := and (forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1).
Definition term28 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((False = x1) /\ (x1 -> x0 = x2)) -> (False /\ x0) = (x1 /\ x2).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((True = x1) /\ (x1 -> x0 = x2)) -> (True /\ x0) = (x1 /\ x2).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x1 -> x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) x3.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) /\ (@FINITE a0 y1)) -> (@CARD a1 (@IMAGE a0 a1 y0 y1)) = (@CARD a0 y1)) x0.
Definition term36 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x1 /\ (x1 -> x0 = x2)) -> x0 = (x1 /\ x2).
Definition term18 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x1 /\ (x1 -> x0 = x2)) -> x0 = (x1 /\ x2)).
Definition term22 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x1 -> x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) True.
Definition term74 (x0 : Prop) (x1 : Prop) := imp ((~ True) /\ (True -> x0 = x1)).
Definition term38 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 /\ (y0 -> x0 = x1)) -> x0 = (y0 /\ x1)) x2.
Definition term43 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (y0 -> x0 = x1)) -> x0 = (y0 /\ x1)) False.
Definition term73 (x0 : Prop) (x1 : Prop) := False /\ (x0 = x1).
Definition term99 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : a1) := (fun y0 : a1 => ((@IN a1 x2 x0) /\ ((@IN a1 y0 x0) /\ ((x1 x2) = (x1 y0)))) -> x2 = y0) x3.
Definition term67 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) /\ (y0 -> x0 = x1)) -> ~ (y0 /\ x1)) x2).
Definition term41 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 /\ (y0 -> x0 = x1)) -> x0 = (y0 /\ x1)) x2).
Definition term75 (x0 : Prop) := ~ (True /\ x0).
