Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term59 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term47 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term45 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> False.
Definition term102 := (~ False) -> False.
Definition term38 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x0 x1).
Definition term40 := @eq nat (NUMERAL 0).
Definition term35 (x0 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0).
Definition term23 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term117 (x0 : nat) := forall y0 : nat, (exists y1 : nat, x0 = (Nat.mul y0 y1)) = (@COND Prop (y0 = (NUMERAL 0)) (x0 = (NUMERAL 0)) ((Nat.modulo x0 y0) = (NUMERAL 0))).
Definition term61 (x0 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> ((Nat.modulo y0 x0) = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term80 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term15 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (exists y0 : nat, x1 = (Nat.mul x0 y0)) = (x1 = (NUMERAL 0)).
Definition term85 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term96 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0))).
Definition term60 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term44 (x0 : Prop) := (~ x0) -> False.
Definition term91 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term86 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term62 (x0 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> ((Nat.modulo y0 x0) = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term46 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term24 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term2 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) (@COND Prop x2 x3 x4).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul x0 y0) x0) = (NUMERAL 0)) x1.
Definition term97 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term49 (x0 : nat) (x1 : nat) := (((~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term52 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term107 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term74 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) (@COND Prop (x1 = (NUMERAL 0)) (x0 = (NUMERAL 0)) ((Nat.modulo x0 x1) = (NUMERAL 0))).
Definition term111 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)).
Definition term100 (x0 : Prop) := (~ x0) -> x0.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term79 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term9 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term16 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : Prop => (exists y1 : nat, x1 = (Nat.mul x0 y1)) = y0) (x1 = (NUMERAL 0))).
Definition term18 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) -> (exists y0 : nat, x0 = (Nat.mul x1 y0)) = (x0 = (NUMERAL 0))) /\ ((~ (x1 = (NUMERAL 0))) -> (exists y0 : nat, x0 = (Nat.mul x1 y0)) = ((Nat.modulo x0 x1) = (NUMERAL 0))).
Definition term94 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term11 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (exists y0 : nat, x0 = (Nat.mul x1 y0)) = ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term116 (x0 : nat) (x1 : nat) := ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> (Nat.modulo x0 x1) = (NUMERAL 0)) /\ (((Nat.modulo x0 x1) = (NUMERAL 0)) -> exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term110 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term39 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term108 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term115 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) -> (Nat.modulo x0 x1) = (NUMERAL 0).
Definition term95 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term22 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term77 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) (x3 : Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term109 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term21 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul x1 y0)) = (@COND Prop (x1 = (NUMERAL 0)) (x0 = (NUMERAL 0)) ((Nat.modulo x0 x1) = (NUMERAL 0)))).
Definition term32 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term13 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term106 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (exists y1 : nat, x1 = (Nat.mul x0 y1)) = y0) (x1 = (NUMERAL 0)).
Definition term112 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (NUMERAL 0).
Definition term4 (x0 : nat) (x1 : nat) := fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0.
Definition term51 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term64 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> ((Nat.modulo y0 x0) = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term63 (x0 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> ((Nat.modulo y0 x0) = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term50 (x0 : nat) (x1 : nat) := (((~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term31 (x0 : Prop) := exists y0 : nat, x0.
Definition term8 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term75 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul x1 y0).
Definition term113 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x1 (Nat.div x0 x1)).
Definition term70 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term76 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term56 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term118 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, y0 = (Nat.mul y1 y2)) = (@COND Prop (y1 = (NUMERAL 0)) (y0 = (NUMERAL 0)) ((Nat.modulo y0 y1) = (NUMERAL 0))).
Definition term88 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term82 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term68 := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo y1 y0) = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term67 := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo y1 y0) = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term53 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term98 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term19 (x0 : nat) (x1 : nat) := @COND Prop (x1 = (NUMERAL 0)) (x0 = (NUMERAL 0)) ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term69 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term20 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) (@COND Prop (x1 = (NUMERAL 0)) (x0 = (NUMERAL 0)) ((Nat.modulo x0 x1) = (NUMERAL 0)))).
Definition term17 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> (exists y0 : nat, x1 = (Nat.mul x0 y0)) = (x1 = (NUMERAL 0))).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : Prop) := (x1 -> (fun y0 : Prop => (exists y1 : nat, x2 = (Nat.mul x3 y1)) = y0) x0) /\ ((~ x1) -> (fun y0 : Prop => (exists y1 : nat, x2 = (Nat.mul x3 y1)) = y0) x4).
Definition term43 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term92 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term58 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term30 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term105 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term114 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (NUMERAL 0)) -> exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term14 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : Prop => (exists y1 : nat, x1 = (Nat.mul x0 y1)) = y0) (x1 = (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term101 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> False.
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo y1 y0) = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x0.
Definition term89 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term34 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0)) x0.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> ((Nat.modulo y0 x0) = (NUMERAL 0)) -> (~ (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0)))) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x1.
Definition term83 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term48 (x0 : nat) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> ((Nat.modulo x0 x1) = (NUMERAL 0)) -> (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term99 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term57 (x0 : nat) (x1 : nat) := imp ((Nat.modulo x0 x1) = (NUMERAL 0)).
Definition term28 (x0 : nat) := fun y0 : nat => x0 = (NUMERAL 0).
Definition term84 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term26 := Nat.mul (NUMERAL 0).
Definition term25 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term6 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) -> (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) (x0 = (NUMERAL 0))) /\ ((~ (x1 = (NUMERAL 0))) -> (fun y0 : Prop => (exists y1 : nat, x0 = (Nat.mul x1 y1)) = y0) ((Nat.modulo x0 x1) = (NUMERAL 0))).
Definition term78 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term0 (x0 : Prop -> Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := x0 (@COND Prop x1 x2 x3).
Definition term73 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term71 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term55 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term33 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term54 (x0 : nat) (x1 : nat) := imp (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term87 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term81 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term72 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term66 := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo y1 y0) = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term65 := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.modulo y1 y0) = (NUMERAL 0)) -> (~ (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0)))) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term29 (x0 : nat) := exists y0 : nat, x0 = (NUMERAL 0).
Definition term93 (x0 : Prop) := x0 -> ~ x0.
Definition term37 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x1 x0) x1.
