Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.mul x0 x1) x2).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (x1 = (NUMERAL 0))) = y0) -> (y0 -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = y1) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = (y0 -> y1)) x3.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.lt (Nat.div x0 x1) x2).
Definition term15 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((~ (x1 = (NUMERAL 0))) = x3) -> (x3 -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = x4) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = (x3 -> x4).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 y0)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.div x0 x1) x2.
Definition term50 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y1 y0) y2) = (Peano.lt y1 (Nat.mul y0 y2)).
Definition term48 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 y1)).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((~ (x2 = (NUMERAL 0))) = (~ (x2 = (NUMERAL 0)))) -> ((~ (x2 = (NUMERAL 0))) -> ((Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = x3) -> ((~ (x2 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = ((~ (x2 = (NUMERAL 0))) -> x3).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = True.
Definition term44 := forall y0 : nat, True.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ (Peano.le (Nat.mul x0 x1) x2)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term42 := fun y0 : nat => True.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((~ (x1 = (NUMERAL 0))) = x3) -> (x3 -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = y0) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = (x3 -> y0).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((~ (x1 = (NUMERAL 0))) = y0) -> (y0 -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = y1) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = (y0 -> y1).
Definition term22 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((~ (x1 = (NUMERAL 0))) = x3) -> (x3 -> ((Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = y0) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2))) = (x3 -> y0)) x4.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((~ (x2 = (NUMERAL 0))) -> ((Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = x3) -> ((~ (x2 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = ((~ (x2 = (NUMERAL 0))) -> x3).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) -> ((Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = True) -> ((~ (x2 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x2) x1) = (Peano.lt x0 (Nat.mul x2 x1))) = ((~ (x2 = (NUMERAL 0))) -> True).
Definition term40 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> True.
Definition term32 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term41 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 y0)).
Definition term46 (x0 : Prop) := forall y0 : nat, x0.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le x0 (Nat.div x1 x2)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.mul x1 x2).
Definition term47 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 y1)).
Definition term49 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y1 y0) y2) = (Peano.lt y1 (Nat.mul y0 y2)).
