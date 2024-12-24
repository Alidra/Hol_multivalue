Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term132 := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (rem (int_add x0 y0) y1) = (rem (int_add (rem x0 y1) (rem y0 y1)) y1)) x1.
Definition term111 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term97 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term139 := int_add (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term129 := ((int_add (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL (BIT0 (BIT1 0))))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term108 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL (BIT1 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term13 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_add y0 y1) y2) = (rem (int_add (rem y0 y2) (rem y1 y2)) y2).
Definition term12 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_add (rem y0 y2) (rem y1 y2)) y2) = (rem (int_add y0 y1) y2).
Definition term64 := @eq int (int_of_num (NUMERAL (BIT1 0))).
Definition term85 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term71 := @eq Prop ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term124 := int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term30 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term143 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term87 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term145 := ((div (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term21 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term128 := rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term51 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term59 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term20 := int_of_num (NUMERAL 0).
Definition term65 := int_add (int_of_num (NUMERAL (BIT1 0))).
Definition term99 := S (Nat.add (BIT1 0) 0).
Definition term120 := ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_add y0 y1) y2) = (rem (int_add (rem y0 y2) (rem y1 y2)) y2)) x0.
Definition term144 := (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term91 := (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term94 := int_lt (int_of_num (NUMERAL 0)).
Definition term140 := int_of_num (Nat.add (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0)).
Definition term122 := int_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term138 := int_add (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0)).
Definition term86 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0)).
Definition term96 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term137 := int_add (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term114 := (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term136 := int_add (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term39 (x0 : int) (x1 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_add x0 x1)).
Definition term35 := (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term34 := (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) /\ (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))).
Definition term98 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term58 := @eq int (int_of_num (NUMERAL 0)).
Definition term60 := rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term31 := fun y0 : int => (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term102 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term142 := Nat.add (NUMERAL (BIT0 (BIT1 0))) (NUMERAL 0).
Definition term133 := int_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term105 := Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term43 (x0 : int) (x1 : int) := rem (int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term68 := rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term54 := rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term46 (x0 : int) (x1 : int) := @eq int (rem (int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term93 := int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term113 := Nat.add (BIT1 0) 0.
Definition term107 := rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term110 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term126 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term38 (x0 : int) (x1 : int) := rem (int_add x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term45 (x0 : int) (x1 : int) := @eq int (rem (int_add x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term109 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term146 (x0 : int) := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_add x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term78 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term112 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term52 (x0 : int) (x1 : int) := rem (int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term29 (x0 : int) := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term73 := rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term49 := int_add (int_of_num (NUMERAL 0)).
Definition term24 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term7 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_add x0 x1) y0) = (rem (int_add (rem x0 y0) (rem x1 y0)) y0).
Definition term6 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_add (rem x0 y0) (rem x1 y0)) y0) = (rem (int_add x0 x1) y0).
Definition term32 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term2 (x0 : int) (x1 : int) (x2 : int) := rem (int_add (rem x0 x2) (rem x1 x2)) x2.
Definition term131 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term79 := rem (int_of_num (NUMERAL 0)).
Definition term37 (x0 : int) (x1 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_add x0 x1).
Definition term82 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term77 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term147 := forall y0 : int, forall y1 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_add y0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y1)).
Definition term15 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_add y0 y1) y2) = (rem (int_add (rem y0 y2) (rem y1 y2)) y2).
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_add (rem y0 y2) (rem y1 y2)) y2) = (rem (int_add y0 y1) y2).
Definition term11 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_add x0 y0) y1) = (rem (int_add (rem x0 y1) (rem y0 y1)) y1).
Definition term10 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_add (rem x0 y1) (rem y0 y1)) y1) = (rem (int_add x0 y0) y1).
Definition term19 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term117 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term92 (x0 : nat) := int_abs (int_of_num x0).
Definition term121 := S (Nat.add 0 0).
Definition term115 := int_lt (int_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_add (rem x0 y0) (rem x1 y0)) y0) = (rem (int_add x0 x1) y0).
Definition term3 (x0 : int) (x1 : int) (x2 : int) := rem (int_add x0 x1) x2.
Definition term83 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term116 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term9 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_add x0 y0) y1) = (rem (int_add (rem x0 y1) (rem y0 y1)) y1).
Definition term8 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_add (rem x0 y1) (rem y0 y1)) y1) = (rem (int_add x0 y0) y1).
Definition term118 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term5 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_add x0 x1) y0) = (rem (int_add (rem x0 y0) (rem x1 y0)) y0).
Definition term123 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term84 := NUMERAL (BIT0 (BIT1 0)).
Definition term25 := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term22 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term36 (x0 : int) := (fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))) x0.
Definition term53 := rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term125 := Nat.add (BIT1 0) (BIT1 0).
Definition term74 := rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term61 := rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : int) := (fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) \/ ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term57 (x0 : int) := @eq int (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term76 := @eq Prop ((rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term70 := @eq Prop ((rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term63 := @eq Prop ((rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term56 := @eq Prop ((rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term47 (x0 : int) (x1 : int) := @eq Prop ((rem (int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term40 (x0 : int) (x1 : int) := @eq Prop ((rem (int_add x0 x1) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term27 := and (forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0)))).
Definition term26 := and (forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term48 (x0 : int) := int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term67 := rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term44 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term104 := Nat.add 0 (BIT1 0).
Definition term100 := BIT0 (BIT1 0).
Definition term23 := fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term72 := int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0))).
Definition term95 := int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term127 := rem (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term106 := rem (int_of_num (NUMERAL (BIT1 0))).
Definition term135 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term81 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term88 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term101 := ((div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term75 := @eq int (rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term69 := @eq int (rem (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term62 := @eq int (rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term55 := @eq int (rem (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term89 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term80 := rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term119 := S (Nat.add 0 (BIT1 0)).
Definition term50 (x0 : int) (x1 : int) := int_add (rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (rem x1 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term41 (x0 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term42 (x0 : int) := @eq Prop ((rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (rem (int_add x0 x1) y0) = (rem (int_add (rem x0 y0) (rem x1 y0)) y0)) x2.
Definition term28 := int_of_num (NUMERAL (BIT1 0)).
Definition term134 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term33 := forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term130 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term103 := NUMERAL (BIT1 0).
Definition term141 := Nat.add (BIT0 (BIT1 0)) 0.
Definition term66 := int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term90 := Peano.le (NUMERAL 0) (NUMERAL 0).
