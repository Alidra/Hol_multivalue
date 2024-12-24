Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) (x1 : int) (x2 : int) := rem (int_mul (rem x0 x2) (rem x1 x2)) x2.
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1)) x1.
Definition term125 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term104 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term114 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term118 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL (BIT1 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term13 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2).
Definition term12 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul (rem y0 y2) (rem y1 y2)) y2) = (rem (int_mul y0 y1) y2).
Definition term66 := @eq int (int_of_num (NUMERAL (BIT1 0))).
Definition term88 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term30 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term94 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term76 := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term77 := rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term91 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term113 := int_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term45 (x0 : int) (x1 : int) := rem (int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term3 (x0 : int) (x1 : int) (x2 : int) := rem (int_mul x0 x1) x2.
Definition term70 := rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term75 := ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))) \/ True.
Definition term120 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term20 := int_of_num (NUMERAL 0).
Definition term106 := S (Nat.add (BIT1 0) 0).
Definition term134 := ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2)) x0.
Definition term98 := (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term101 := int_lt (int_of_num (NUMERAL 0)).
Definition term90 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0)).
Definition term50 (x0 : int) := int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term103 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term128 := (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term35 := (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term34 := (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) /\ (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))).
Definition term105 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term60 := @eq int (int_of_num (NUMERAL 0)).
Definition term31 := fun y0 : int => (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term121 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term78 := rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term63 := rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term123 := Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term48 (x0 : int) (x1 : int) := @eq int (rem (int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term100 := int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term127 := Nat.add (BIT1 0) 0.
Definition term117 := rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 (x0 : int) (x1 : int) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term124 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term47 (x0 : int) (x1 : int) := @eq int (rem (int_mul x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term110 (x0 : nat) := int_mul (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term119 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term136 (x0 : int) := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term55 := rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term68 := int_mul (int_of_num (NUMERAL (BIT1 0))).
Definition term93 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term126 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term115 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term38 (x0 : int) (x1 : int) := rem (int_mul x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term29 (x0 : int) := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term89 := int_add (int_of_num (NUMERAL 0)).
Definition term69 := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term24 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term7 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0).
Definition term6 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_mul (rem x0 y0) (rem x1 y0)) y0) = (rem (int_mul x0 x1) y0).
Definition term74 := or ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term32 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term112 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term83 := rem (int_of_num (NUMERAL 0)).
Definition term39 (x0 : int) (x1 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 x1)).
Definition term54 (x0 : int) (x1 : int) := rem (int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term82 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term37 (x0 : int) (x1 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 x1).
Definition term92 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term137 := forall y0 : int, forall y1 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul y0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y1)).
Definition term15 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2).
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_mul (rem y0 y2) (rem y1 y2)) y2) = (rem (int_mul y0 y1) y2).
Definition term11 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1).
Definition term10 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_mul (rem x0 y1) (rem y0 y1)) y1) = (rem (int_mul x0 y0) y1).
Definition term19 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term131 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term99 (x0 : nat) := int_abs (int_of_num x0).
Definition term135 := S (Nat.add 0 0).
Definition term129 := int_lt (int_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_mul (rem x0 y0) (rem x1 y0)) y0) = (rem (int_mul x0 x1) y0).
Definition term86 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term130 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term9 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1).
Definition term8 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_mul (rem x0 y1) (rem y0 y1)) y1) = (rem (int_mul x0 y0) y1).
Definition term132 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term5 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0).
Definition term87 := NUMERAL (BIT0 (BIT1 0)).
Definition term41 (x0 : int) := or (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term25 := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term22 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term36 (x0 : int) := (fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) x0.
Definition term0 (x0 : int) := (fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term44 (x0 : int) (x1 : int) := ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term59 (x0 : int) := @eq int (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term80 := @eq Prop ((rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term73 := @eq Prop ((rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term65 := @eq Prop ((rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term58 := @eq Prop ((rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term49 (x0 : int) (x1 : int) := @eq Prop ((rem (int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term40 (x0 : int) (x1 : int) := @eq Prop ((rem (int_mul x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term27 := and (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term26 := and (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term46 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term122 := Nat.add 0 (BIT1 0).
Definition term107 := BIT0 (BIT1 0).
Definition term23 := fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term102 := int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term61 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term67 := True \/ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term116 := rem (int_of_num (NUMERAL (BIT1 0))).
Definition term85 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term95 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term108 := ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term53 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term62 := rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term79 := @eq int (rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term72 := @eq int (rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term64 := @eq int (rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term57 := @eq int (rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term96 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term42 (x0 : int) := or ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term81 := ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))) \/ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term52 (x0 : int) (x1 : int) := int_mul (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term51 := int_mul (int_of_num (NUMERAL 0)).
Definition term84 := rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term133 := S (Nat.add 0 (BIT1 0)).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0)) x2.
Definition term28 := int_of_num (NUMERAL (BIT1 0)).
Definition term33 := forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term111 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term109 := NUMERAL (BIT1 0).
Definition term71 := rem (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term56 := rem (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 := Peano.le (NUMERAL 0) (NUMERAL 0).
