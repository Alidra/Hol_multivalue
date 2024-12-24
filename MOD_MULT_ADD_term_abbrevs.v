Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term137 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term50 (x0 : Prop) := imp ((True -> x0) /\ True).
Definition term117 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1))).
Definition term147 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term144 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term139 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term88 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) x0.
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) x0.
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, ((Nat.add (Nat.mul x0 x2) x1) = (Nat.add (Nat.mul y0 x2) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.modulo x1 x2) x2)) -> (Nat.modulo (Nat.add (Nat.mul x0 x2) x1) x2) = (Nat.modulo x1 x2).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul (Nat.div x1 x2) x2).
Definition term128 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term31 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term98 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x2)) /\ (Peano.lt x2 x1)) -> (Nat.modulo x0 x1) = x2.
Definition term126 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add x0 (Nat.mul x1 x2)) x2.
Definition term114 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)).
Definition term66 (x0 : Prop) (x1 : Prop) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) = x0) -> (x0 -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = x1) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = (x0 -> x1).
Definition term55 (x0 : Prop) (x1 : Prop) := (((x0 -> x1) /\ x0) -> x0 /\ x1) -> ((x0 -> x1) /\ x0) -> x0 /\ x1.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0.
Definition term142 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0) x2.
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.add x0 (Nat.mul x2 x1)) x2).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.add x0 (Nat.mul x1 x2)) x2).
Definition term86 (x0 : Prop) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) = (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1))) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = x0) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> x0).
Definition term56 := (((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term135 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term109 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.add y0 (Nat.mul x1 x0)) x1) = (Nat.modulo y0 x1).
Definition term96 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.add (Nat.mul x1 x0) y0) x1) = (Nat.modulo y0 x1).
Definition term78 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.add y0 (Nat.mul x0 x1)) x1) = (Nat.modulo y0 x1).
Definition term77 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.add (Nat.mul x0 x1) y0) x1) = (Nat.modulo y0 x1).
Definition term118 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> True.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term54 (x0 : Prop) (x1 : Prop) := (((x0 -> x1) /\ x0) -> x0 /\ x1) -> x0 /\ x1.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term63 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y3) y4) y3) = (Nat.modulo y4 y3)) = y0) -> (y0 -> ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y3 y2) y4) y3) = (Nat.modulo y4 y3)) /\ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y2 y3)) y3) = (Nat.modulo y4 y3)) /\ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y3 y2)) y3) = (Nat.modulo y4 y3)))) = y1) -> ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y3) y4) y3) = (Nat.modulo y4 y3)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y3 y2) y4) y3) = (Nat.modulo y4 y3)) /\ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y2 y3)) y3) = (Nat.modulo y4 y3)) /\ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y3 y2)) y3) = (Nat.modulo y4 y3)))) = (y0 -> y1)) x0.
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term93 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul x0 x2) x1) = (Nat.add (Nat.mul (Nat.add x0 (Nat.div x1 x2)) x2) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.modulo x1 x2) x2).
Definition term149 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term145 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term141 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term89 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.add y1 (Nat.mul x0 y0)) y0) = (Nat.modulo y1 y0)) x1.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1) x1.
Definition term37 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term110 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.add y1 (Nat.mul y0 x0)) y0) = (Nat.modulo y1 y0).
Definition term100 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.add (Nat.mul y0 x0) y1) y0) = (Nat.modulo y1 y0).
Definition term80 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.add y1 (Nat.mul x0 y0)) y0) = (Nat.modulo y1 y0).
Definition term79 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.add (Nat.mul x0 y0) y1) y0) = (Nat.modulo y1 y0).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term172 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))).
Definition term41 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1.
Definition term162 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term59 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term58 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1))).
Definition term124 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term47 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) False.
Definition term48 (x0 : Prop) := ((False -> x0) /\ False) -> False /\ x0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> (Nat.modulo x1 x2) = x3.
Definition term115 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = True.
Definition term121 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term42 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) True.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0) x3.
Definition term46 (x0 : Prop) (x1 : Prop) := @eq Prop (((x0 -> x1) /\ x0) -> x0 /\ x1).
Definition term148 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term140 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term113 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1).
Definition term111 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.add y1 (Nat.mul y0 x0)) y0) = (Nat.modulo y1 y0).
Definition term103 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1).
Definition term101 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.add (Nat.mul y0 x0) y1) y0) = (Nat.modulo y1 y0).
Definition term85 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1).
Definition term82 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.add y1 (Nat.mul x0 y0)) y0) = (Nat.modulo y1 y0).
Definition term81 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.add (Nat.mul x0 y0) y1) y0) = (Nat.modulo y1 y0).
Definition term57 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1).
Definition term30 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term29 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1.
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1.
Definition term16 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2.
Definition term14 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3.
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term138 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term129 (x0 : nat) := @eq nat (Nat.modulo x0 (NUMERAL 0)).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul (Nat.div x1 x2) x2)) (Nat.modulo x1 x2).
Definition term40 (x0 : Prop) := fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0.
Definition term36 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term52 (x0 : Prop) := imp ((False -> x0) /\ False).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1) x2.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2) x1.
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul x0 x1) x2).
Definition term45 (x0 : Prop) (x1 : Prop) := ((x0 -> x1) /\ x0) -> x0 /\ x1.
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term97 := forall y0 : nat, True.
Definition term134 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul (Nat.div x1 x2) x2)).
Definition term119 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term120 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> (Nat.modulo x0 x1) = x2.
Definition term51 (x0 : Prop) := (False -> x0) /\ False.
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term171 := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)).
Definition term95 := fun y0 : nat => True.
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 (Nat.div x1 x2)) x2) (Nat.modulo x1 x2).
Definition term44 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1).
Definition term108 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.add y0 (Nat.mul x1 x0)) x1) = (Nat.modulo y0 x1).
Definition term94 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.add (Nat.mul x1 x0) y0) x1) = (Nat.modulo y0 x1).
Definition term76 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.add y0 (Nat.mul x0 x1)) x1) = (Nat.modulo y0 x1).
Definition term75 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.add (Nat.mul x0 x1) y0) x1) = (Nat.modulo y0 x1).
Definition term64 (x0 : Prop) := forall y0 : Prop, ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y2) y3) y2) = (Nat.modulo y3 y2)) = x0) -> (x0 -> ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y1) y3) y2) = (Nat.modulo y3 y2)) /\ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y1 y2)) y2) = (Nat.modulo y3 y2)) /\ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y2 y1)) y2) = (Nat.modulo y3 y2)))) = y0) -> ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y2) y3) y2) = (Nat.modulo y3 y2)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y1) y3) y2) = (Nat.modulo y3 y2)) /\ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y1 y2)) y2) = (Nat.modulo y3 y2)) /\ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y2 y1)) y2) = (Nat.modulo y3 y2)))) = (x0 -> y0).
Definition term60 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.add y0 (Nat.mul x0 x1)) x1) = (Nat.modulo y0 x1)) x2.
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term39 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term62 := forall y0 : Prop, forall y1 : Prop, ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y3) y4) y3) = (Nat.modulo y4 y3)) = y0) -> (y0 -> ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y3 y2) y4) y3) = (Nat.modulo y4 y3)) /\ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y2 y3)) y3) = (Nat.modulo y4 y3)) /\ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y3 y2)) y3) = (Nat.modulo y4 y3)))) = y1) -> ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y3) y4) y3) = (Nat.modulo y4 y3)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add (Nat.mul y3 y2) y4) y3) = (Nat.modulo y4 y3)) /\ ((forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y2 y3)) y3) = (Nat.modulo y4 y3)) /\ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.modulo (Nat.add y4 (Nat.mul y3 y2)) y3) = (Nat.modulo y4 y3)))) = (y0 -> y1).
Definition term61 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add (Nat.mul x2 x0) x1) x2.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add (Nat.mul x0 x2) x1) x2.
Definition term49 (x0 : Prop) := (True -> x0) /\ True.
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.add (Nat.mul x2 x0) x1) x2).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.add (Nat.mul x0 x2) x1) x2).
Definition term127 := Nat.add (NUMERAL 0).
Definition term105 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)).
Definition term104 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)).
Definition term164 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) = True.
Definition term131 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term53 (x0 : Prop) (x1 : Prop) := (x1 -> x0) /\ x1.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add (Nat.mul x0 x1) x2).
Definition term123 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add x0 (Nat.mul x1 x2)).
Definition term87 (x0 : Prop) := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = x0) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> x0).
Definition term125 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term166 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 x1) x1) = True.
Definition term150 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term43 (x0 : Prop) := ((True -> x0) /\ True) -> True /\ x0.
Definition term154 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.add x0 (Nat.mul x2 x1)) x2.
Definition term136 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term133 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term116 := ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = True) -> ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1)))) = ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1)) -> True).
Definition term99 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 (Nat.div x1 x2)) x2).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 (Nat.div x1 x2)) x2.
Definition term65 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y2) y3) y2) = (Nat.modulo y3 y2)) = x0) -> (x0 -> ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y1) y3) y2) = (Nat.modulo y3 y2)) /\ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y1 y2)) y2) = (Nat.modulo y3 y2)) /\ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y2 y1)) y2) = (Nat.modulo y3 y2)))) = y0) -> ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y2) y3) y2) = (Nat.modulo y3 y2)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add (Nat.mul y2 y1) y3) y2) = (Nat.modulo y3 y2)) /\ ((forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y1 y2)) y2) = (Nat.modulo y3 y2)) /\ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.modulo (Nat.add y3 (Nat.mul y2 y1)) y2) = (Nat.modulo y3 y2)))) = (x0 -> y0)) x1.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.add (Nat.mul x0 x2) x1) = (Nat.add (Nat.mul (Nat.add x0 (Nat.div x1 x2)) x2) (Nat.modulo x1 x2))).
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, ((Nat.add (Nat.mul x0 x2) x1) = (Nat.add (Nat.mul y0 x2) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.modulo x1 x2) x2).
Definition term38 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term132 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Nat.add (Nat.mul x0 x2) x1) = (Nat.add (Nat.mul y0 x2) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.modulo x1 x2) x2).
Definition term122 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.div x1 x2).
Definition term35 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term112 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y1 y0)) y1) = (Nat.modulo y2 y1).
Definition term102 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y1 y0) y2) y1) = (Nat.modulo y2 y1).
Definition term84 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add y2 (Nat.mul y0 y1)) y1) = (Nat.modulo y2 y1).
Definition term83 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.add (Nat.mul y0 y1) y2) y1) = (Nat.modulo y2 y1).
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.mul x1 x2).
