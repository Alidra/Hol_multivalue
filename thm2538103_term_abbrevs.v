Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term146 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term81 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0).
Definition term12 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term39 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = (int_add (int_mul x1 x3) x2)) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x3))).
Definition term48 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1)) x2.
Definition term35 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1)) x2.
Definition term100 (x0 : nat) := @eq Prop ((forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) /\ (forall y0 : nat, (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0)))).
Definition term99 (x0 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0)).
Definition term76 := @eq Prop ((forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1)))).
Definition term75 := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0)).
Definition term85 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0) /\ ((fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0).
Definition term59 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0).
Definition term136 (x0 : nat) (x1 : nat) := and ((int_of_num x0) = (int_add (int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1)) (int_of_num (Nat.modulo x0 x1)))).
Definition term105 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0) /\ ((fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0).
Definition term118 := int_of_num (NUMERAL 0).
Definition term47 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2)) x1.
Definition term33 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2)) x1.
Definition term90 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term111 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term8 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term97 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0.
Definition term91 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0.
Definition term84 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0).
Definition term58 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0).
Definition term74 := (forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))).
Definition term123 (x0 : nat) := rem (int_of_num x0).
Definition term124 (x0 : nat) := rem (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term46 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3)) x0.
Definition term31 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) x0.
Definition term102 (x0 : nat) (x1 : nat) := and ((div (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.div x0 x1))).
Definition term14 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term10 (x0 : nat) := forall y0 : nat, (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0).
Definition term137 (x0 : nat) (x1 : nat) := and ((int_of_num x0) = (int_of_num (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term98 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (rem (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.modulo x0 y1))) y0.
Definition term92 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0.
Definition term131 (x0 : nat) (x1 : nat) := int_add (int_of_num (Nat.mul (Nat.div x0 x1) x1)).
Definition term36 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0).
Definition term128 (x0 : nat) (x1 : nat) := int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1).
Definition term57 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term122 := @eq int (int_of_num (NUMERAL 0)).
Definition term82 := fun y0 : nat => (forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ (forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term110 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term6 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term141 (x0 : nat) (x1 : nat) := and (int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))).
Definition term150 (x0 : nat) (x1 : nat) := True /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term129 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul (Nat.div x0 x1) x1).
Definition term87 (x0 : nat) := fun y0 : nat => (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0)).
Definition term139 (x0 : nat) (x1 : nat) := int_lt (int_of_num (Nat.modulo x0 x1)) (int_abs (int_of_num x1)).
Definition term120 (x0 : nat) := div (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term5 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term106 (x0 : nat) := fun y0 : nat => ((div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) /\ ((rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))).
Definition term135 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term16 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term148 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1)).
Definition term89 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term112 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term95 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_of_num x1).
Definition term78 (x0 : nat) := and (forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))).
Definition term145 (x0 : nat) (x1 : nat) := ((int_of_num x0) = (int_of_num (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))) /\ (int_lt (int_of_num (Nat.modulo x0 x1)) (int_of_num x1))).
Definition term119 (x0 : nat) := div (int_of_num x0).
Definition term104 (x0 : nat) (x1 : nat) := ((div (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.div x0 x1))) /\ ((rem (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.modulo x0 x1))).
Definition term138 (x0 : nat) (x1 : nat) := int_lt (int_of_num (Nat.modulo x0 x1)).
Definition term29 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term109 := forall y0 : nat, forall y1 : nat, ((div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ ((rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))).
Definition term73 := forall y0 : nat, forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1)).
Definition term66 := forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term0 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term142 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))) /\ (int_lt (int_of_num (Nat.modulo x0 x1)) (int_abs (int_of_num x1))).
Definition term79 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))) x0).
Definition term50 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term96 (x0 : nat) (x1 : nat) := int_of_num (Nat.modulo x0 x1).
Definition term4 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term86 (x0 : nat) := fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term44 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term43 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2).
Definition term42 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1).
Definition term34 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1).
Definition term32 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2).
Definition term30 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term19 (x0 : nat) := int_abs (int_of_num x0).
Definition term147 (x0 : nat) (x1 : nat) := and (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term117 (x0 : int) := div x0 (int_of_num (NUMERAL 0)).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term121 (x0 : nat) (x1 : nat) := @eq int (div (int_of_num x0) (int_of_num x1)).
Definition term103 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) x1) /\ ((fun y0 : nat => (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))) x1).
Definition term56 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term70 (x0 : nat) := forall y0 : nat, (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0)).
Definition term63 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term26 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term21 (x0 : nat) := forall y0 : nat, (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term133 (x0 : nat) (x1 : nat) := int_add (int_of_num (Nat.mul (Nat.div x0 x1) x1)) (int_of_num (Nat.modulo x0 x1)).
Definition term144 (x0 : nat) (x1 : nat) := ((int_of_num x0) = (int_add (int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1)) (int_of_num (Nat.modulo x0 x1)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))) /\ (int_lt (int_of_num (Nat.modulo x0 x1)) (int_abs (int_of_num x1)))).
Definition term126 (x0 : nat) := @eq int (int_of_num x0).
Definition term45 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term17 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term37 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0)) x3.
Definition term134 (x0 : nat) (x1 : nat) := int_of_num (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term80 (x0 : nat) := (forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) /\ (forall y0 : nat, (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))).
Definition term68 := and (forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))).
Definition term132 (x0 : nat) (x1 : nat) := int_add (int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1)) (int_of_num (Nat.modulo x0 x1)).
Definition term71 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0.
Definition term64 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0.
Definition term18 (x0 : nat) := (fun y0 : nat => (int_abs (int_of_num y0)) = (int_of_num y0)) x0.
Definition term69 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))) x0.
Definition term62 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1))) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_lt (int_of_num y0) (int_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term94 (x0 : nat) (x1 : nat) := (fun y0 : nat => (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))) x1.
Definition term88 (x0 : nat) (x1 : nat) := (fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) x1.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0))) x1.
Definition term38 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = (int_add (int_mul x0 x2) x3)) /\ ((int_le (int_of_num (NUMERAL 0)) x3) /\ (int_lt x3 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term130 (x0 : nat) (x1 : nat) := int_add (int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1)).
Definition term7 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term125 (x0 : nat) (x1 : nat) := @eq int (rem (int_of_num x0) (int_of_num x1)).
Definition term116 (x0 : int) := (fun y0 : int => (div y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term93 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (div (int_of_num x0) (int_of_num y1)) = (int_of_num (Nat.div x0 y1))) y0).
Definition term67 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0).
Definition term77 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) x0).
Definition term107 (x0 : nat) := forall y0 : nat, ((div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) /\ ((rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))).
Definition term151 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term149 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term41 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term115 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term61 := fun y0 : nat => forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1)).
Definition term60 := fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term83 := forall y0 : nat, (forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ (forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))).
Definition term101 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) x1).
Definition term40 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term114 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term24 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term140 (x0 : nat) (x1 : nat) := int_lt (int_of_num (Nat.modulo x0 x1)) (int_of_num x1).
Definition term127 (x0 : nat) (x1 : nat) := (((int_of_num x0) = (int_add (int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1)) (int_of_num (Nat.modulo x0 x1)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))) /\ (int_lt (int_of_num (Nat.modulo x0 x1)) (int_abs (int_of_num x1))))) -> ((div (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.div x0 x1))) /\ ((rem (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.modulo x0 x1))).
Definition term2 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term113 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term72 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (rem (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.modulo y1 y2))) y0.
Definition term65 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (div (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.div y1 y2))) y0.
Definition term143 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.modulo x0 x1))) /\ (int_lt (int_of_num (Nat.modulo x0 x1)) (int_of_num x1)).
Definition term28 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term49 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term108 := fun y0 : nat => forall y1 : nat, ((div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) /\ ((rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))).
