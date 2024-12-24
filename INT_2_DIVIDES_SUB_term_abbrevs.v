Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (rem (int_sub x0 y0) y1) = (rem (int_sub (rem x0 y1) (rem y0 y1)) y1)) x1.
Definition term118 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num x1).
Definition term137 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term48 (x0 : int) := int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term102 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term155 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL (BIT1 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term13 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_sub y0 y1) y2) = (rem (int_sub (rem y0 y2) (rem y1 y2)) y2).
Definition term12 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_sub (rem y0 y2) (rem y1 y2)) y2) = (rem (int_sub y0 y1) y2).
Definition term64 := @eq int (int_of_num (NUMERAL (BIT1 0))).
Definition term90 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term71 := @eq Prop ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term133 := int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term30 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term92 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term21 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term81 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term125 := int_neg (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term157 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term20 := int_of_num (NUMERAL 0).
Definition term108 := int_add (int_of_num (NUMERAL 0)) (int_neg (int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0))))).
Definition term107 := int_add (int_of_num (NUMERAL 0)) (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term66 := int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term149 := int_add (int_of_num (NUMERAL (BIT1 0))).
Definition term104 := S (Nat.add (BIT1 0) 0).
Definition term65 := int_sub (int_of_num (NUMERAL (BIT1 0))).
Definition term160 := ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_sub y0 y1) y2) = (rem (int_sub (rem y0 y2) (rem y1 y2)) y2)) x0.
Definition term37 (x0 : int) (x1 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_sub x0 x1).
Definition term96 := (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term99 := int_lt (int_of_num (NUMERAL 0)).
Definition term151 := int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term59 := int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term91 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0)).
Definition term101 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term159 := (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term140 := (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ ((rem (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term35 := (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term34 := (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) /\ (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))).
Definition term103 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term58 := @eq int (int_of_num (NUMERAL 0)).
Definition term31 := fun y0 : int => (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term113 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term74 := rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term61 := rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term124 := int_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term146 := ((div (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ ((rem (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term126 := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term112 := Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term46 (x0 : int) (x1 : int) := @eq int (rem (int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term2 (x0 : int) (x1 : int) (x2 : int) := rem (int_sub (rem x0 x2) (rem x1 x2)) x2.
Definition term98 := int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term139 := Nat.add (BIT1 0) 0.
Definition term154 := rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term158 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term136 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ ((rem (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term132 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term135 := int_add (int_neg (int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))))).
Definition term45 (x0 : int) (x1 : int) := @eq int (rem (int_sub x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term156 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term128 := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term163 (x0 : int) := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_sub x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term3 (x0 : int) (x1 : int) (x2 : int) := rem (int_sub x0 x1) x2.
Definition term129 := int_add (int_neg (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term83 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term138 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term52 (x0 : int) (x1 : int) := rem (int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term109 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term161 := int_add (int_of_num (NUMERAL (BIT1 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term29 (x0 : int) := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term134 := int_neg (int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term80 := int_add (int_of_num (NUMERAL 0)).
Definition term72 := int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0))).
Definition term78 := int_add (int_of_num (NUMERAL 0)) (int_neg (int_of_num (NUMERAL 0))).
Definition term24 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term7 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_sub x0 x1) y0) = (rem (int_sub (rem x0 y0) (rem x1 y0)) y0).
Definition term6 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_sub (rem x0 y0) (rem x1 y0)) y0) = (rem (int_sub x0 x1) y0).
Definition term32 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term49 := int_sub (int_of_num (NUMERAL 0)).
Definition term84 := rem (int_of_num (NUMERAL 0)).
Definition term115 := rem (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term120 := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term87 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term148 := int_add (int_of_num (NUMERAL (BIT1 0))) (int_neg (int_of_num (NUMERAL 0))).
Definition term82 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term116 := rem (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term164 := forall y0 : int, forall y1 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_sub y0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y1)).
Definition term15 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_sub y0 y1) y2) = (rem (int_sub (rem y0 y2) (rem y1 y2)) y2).
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_sub (rem y0 y2) (rem y1 y2)) y2) = (rem (int_sub y0 y1) y2).
Definition term11 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_sub x0 y0) y1) = (rem (int_sub (rem x0 y1) (rem y0 y1)) y1).
Definition term10 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_sub (rem x0 y1) (rem y0 y1)) y1) = (rem (int_sub x0 y0) y1).
Definition term19 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term143 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 (x0 : nat) := int_abs (int_of_num x0).
Definition term147 := S (Nat.add 0 0).
Definition term141 := int_lt (int_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_sub (rem x0 y0) (rem x1 y0)) y0) = (rem (int_sub x0 x1) y0).
Definition term88 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term142 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term127 := int_add (int_neg (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term9 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_sub x0 y0) y1) = (rem (int_sub (rem x0 y1) (rem y0 y1)) y1).
Definition term8 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_sub (rem x0 y1) (rem y0 y1)) y1) = (rem (int_sub x0 y0) y1).
Definition term144 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term79 := int_neg (int_of_num (NUMERAL 0)).
Definition term67 := rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term5 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_sub x0 x1) y0) = (rem (int_sub (rem x0 y0) (rem x1 y0)) y0).
Definition term152 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term68 := rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term54 := rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term130 := int_add (int_neg (int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term89 := NUMERAL (BIT0 (BIT1 0)).
Definition term25 := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term22 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term36 (x0 : int) := (fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) x0.
Definition term131 := Nat.add (BIT1 0) (BIT1 0).
Definition term117 := ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ ((rem (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : int) := (fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term119 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.mul x0 x1)).
Definition term57 (x0 : int) := @eq int (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term121 := int_neg (int_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))))).
Definition term53 := rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term76 := @eq Prop ((rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term70 := @eq Prop ((rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term63 := @eq Prop ((rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term56 := @eq Prop ((rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term47 (x0 : int) (x1 : int) := @eq Prop ((rem (int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term40 (x0 : int) (x1 : int) := @eq Prop ((rem (int_sub x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term27 := and (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term26 := and (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term77 (x0 : int) (x1 : int) := int_add x0 (int_neg x1).
Definition term60 := rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term44 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term162 (x0 : nat) := int_add (int_of_num x0) (int_neg (int_of_num x0)).
Definition term111 := Nat.add 0 (BIT1 0).
Definition term105 := BIT0 (BIT1 0).
Definition term23 := fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term38 (x0 : int) (x1 : int) := rem (int_sub x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term100 := int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term51 := int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term153 := rem (int_of_num (NUMERAL (BIT1 0))).
Definition term39 (x0 : int) (x1 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_sub x0 x1)).
Definition term123 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term73 := rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term86 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term93 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term106 := ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term114 := int_neg (int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)))).
Definition term50 (x0 : int) (x1 : int) := int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term75 := @eq int (rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term69 := @eq int (rem (int_sub (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term62 := @eq int (rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term55 := @eq int (rem (int_sub (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term94 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term85 := rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term145 := S (Nat.add 0 (BIT1 0)).
Definition term41 (x0 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term43 (x0 : int) (x1 : int) := rem (int_sub (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term42 (x0 : int) := @eq Prop ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (rem (int_sub x0 x1) y0) = (rem (int_sub (rem x0 y0) (rem x1 y0)) y0)) x2.
Definition term28 := int_of_num (NUMERAL (BIT1 0)).
Definition term122 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term33 := forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term110 := NUMERAL (BIT1 0).
Definition term150 := int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term95 := Peano.le (NUMERAL 0) (NUMERAL 0).
