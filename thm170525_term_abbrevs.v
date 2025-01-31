Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1.
Definition term52 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0) /\ ((fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0).
Definition term94 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x0 x1).
Definition term61 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0.
Definition term32 := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0).
Definition term69 (x0 : nat) := @eq Prop ((forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) /\ (forall y0 : nat, (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0))).
Definition term68 (x0 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0)).
Definition term47 := @eq Prop ((forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ (forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0))).
Definition term46 := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0)).
Definition term56 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0) /\ ((fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0).
Definition term30 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0) /\ ((fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0).
Definition term84 := @eq nat (NUMERAL 0).
Definition term81 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term41 (x0 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) x0.
Definition term60 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 x1) x0) = x1.
Definition term74 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0) /\ ((fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0).
Definition term15 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term55 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0).
Definition term29 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0).
Definition term45 := (forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ (forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)).
Definition term90 := Nat.div (NUMERAL 0) (NUMERAL 0).
Definition term82 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term79 (x0 : nat) := (fun y0 : nat => (Nat.modulo (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term103 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) = (~ (y0 = (NUMERAL 0)))) x0.
Definition term67 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0.
Definition term62 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0.
Definition term64 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)) x1.
Definition term28 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term87 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x0 x1).
Definition term53 := fun y0 : nat => (forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ (forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term107 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term34 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0.
Definition term96 := Nat.modulo (NUMERAL 0) (NUMERAL 0).
Definition term85 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term112 (x0 : nat) (x1 : nat) := ((Nat.mul x1 x0) = (Nat.add (Nat.mul x0 x1) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x1).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term108 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0)) x3.
Definition term80 (x0 : nat) := Nat.modulo (NUMERAL 0) x0.
Definition term97 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.mul x1 x0) x1).
Definition term21 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term31 := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1.
Definition term89 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x1 x0) x1.
Definition term100 (x0 : nat) (x1 : nat) := and ((Nat.div (Nat.mul x0 x1) x0) = x1).
Definition term92 := @eq nat (Nat.div (NUMERAL 0) (NUMERAL 0)).
Definition term71 (x0 : nat) (x1 : nat) := and ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 x1) x0) = x1).
Definition term106 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term58 (x0 : nat) := fun y0 : nat => (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0).
Definition term95 := Nat.modulo (NUMERAL 0).
Definition term75 (x0 : nat) := fun y0 : nat => ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) /\ ((Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)).
Definition term49 (x0 : nat) := and (forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0).
Definition term73 (x0 : nat) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.mul x1 x0) x1) = x0) /\ ((Nat.modulo (Nat.mul x1 x0) x1) = (NUMERAL 0)).
Definition term91 (x0 : nat) (x1 : nat) := @eq nat (Nat.div (Nat.mul x1 x0) x1).
Definition term78 := forall y0 : nat, forall y1 : nat, ((~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ ((Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)).
Definition term44 := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0).
Definition term37 := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1.
Definition term14 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term13 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3).
Definition term50 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0) /\ ((fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)) x0).
Definition term20 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term76 (x0 : nat) := forall y0 : nat, ((~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) /\ ((Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1)) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1)) x2.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2)) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2)) x1.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term88 := Nat.div (NUMERAL 0).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term99 (x0 : nat) (x1 : nat) := True -> (Nat.div (Nat.mul x0 x1) x0) = x1.
Definition term72 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1) /\ ((fun y0 : nat => (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)) x1).
Definition term27 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term105 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term51 (x0 : nat) := (forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) /\ (forall y0 : nat, (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)).
Definition term39 := and (forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1).
Definition term42 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0.
Definition term35 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0).
Definition term57 (x0 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0.
Definition term66 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.modulo (Nat.mul x0 y1) x0) = (NUMERAL 0)) y0.
Definition term102 (x0 : nat) (x1 : nat) := (((Nat.mul x1 x0) = (Nat.add (Nat.mul x0 x1) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) x1)) -> ((Nat.div (Nat.mul x1 x0) x1) = x0) /\ ((Nat.modulo (Nat.mul x1 x0) x1) = (NUMERAL 0)).
Definition term63 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y1) x0) = y1) y0).
Definition term38 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0).
Definition term48 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) x0).
Definition term98 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term110 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term54 := forall y0 : nat, (forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ (forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)).
Definition term86 := Nat.mul (NUMERAL 0).
Definition term83 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term70 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Nat.div (Nat.mul x0 y0) x0) = y0) x1).
Definition term109 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) (NUMERAL 0).
Definition term43 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.modulo (Nat.mul y1 y2) y1) = (NUMERAL 0)) y0.
Definition term36 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.mul y1 y2) y1) = y2) y0.
Definition term111 (x0 : nat) (x1 : nat) := and ((Nat.mul x1 x0) = (Nat.add (Nat.mul x0 x1) (NUMERAL 0))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term93 (x0 : nat) := False -> (Nat.div (NUMERAL 0) (NUMERAL 0)) = x0.
Definition term104 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term19 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term77 := fun y0 : nat => forall y1 : nat, ((~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.mul y0 y1) y0) = y1) /\ ((Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)).
Definition term101 (x0 : nat) (x1 : nat) := ((Nat.div (Nat.mul x1 x0) x1) = x0) /\ ((Nat.modulo (Nat.mul x1 x0) x1) = (NUMERAL 0)).
Definition term65 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x1 x0) x1.
