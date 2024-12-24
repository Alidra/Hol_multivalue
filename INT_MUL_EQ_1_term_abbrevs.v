Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : nat) := real_sub (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term198 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num x1).
Definition term208 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0))) x1.
Definition term26 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term215 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term146 (x0 : nat) := real_sub (real_neg (real_of_num x0)).
Definition term37 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term57 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term107 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term25 (x0 : nat) := real_neg (real_of_num x0).
Definition term135 (x0 : nat) := ~ ((real_of_num x0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term7 (x0 : Prop) := ~ (~ x0).
Definition term210 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_neg (int_of_num x1)).
Definition term23 := real_of_num (NUMERAL 0).
Definition term195 (x0 : int) (x1 : int) := int_mul (int_neg x0) x1.
Definition term179 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0)))).
Definition term193 (x0 : int) := forall y0 : int, (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0)).
Definition term205 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ False.
Definition term106 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term159 (x0 : int) := (exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0))).
Definition term145 (x0 : nat) := real_sub (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term48 (x0 : nat) := real_ge (real_of_num x0) (real_of_num (NUMERAL 0)).
Definition term16 := real_neg (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term124 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term206 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 (int_neg y1)) = (int_neg (int_mul y0 y1))) x0.
Definition term192 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_neg y0) y1) = (int_neg (int_mul y0 y1))) x0.
Definition term186 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_neg y0) = y1) = (y0 = (int_neg y1))) x0.
Definition term75 (x0 : nat) := (fun y0 : real => (real_mul y0 (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term79 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 (x0 : int) (x1 : int) := (x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (x1 = (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term6 (x0 : nat) := ~ ((int_of_num x0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term99 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : nat) := @eq real (real_of_int (int_of_num x0)).
Definition term185 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))) \/ False.
Definition term163 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term157 (x0 : nat) := ~ ((real_neg (real_of_num x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term129 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term104 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term103 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term115 (x0 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num x0)).
Definition term52 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term76 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term96 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term90 (x0 : nat) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num x0) (real_of_num (NUMERAL 0))).
Definition term218 (x0 : int) (x1 : int) := ((exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0)))) -> ((int_mul x0 x1) = (int_of_num (NUMERAL (BIT1 0)))) = (((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0))))) \/ ((x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (x1 = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
Definition term149 (x0 : nat) := @eq real (real_sub (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term83 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term27 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term201 (x0 : nat) (x1 : nat) := @eq int (int_neg (int_of_num (Nat.mul x0 x1))).
Definition term121 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term207 (x0 : int) := forall y0 : int, (int_mul x0 (int_neg y0)) = (int_neg (int_mul x0 y0)).
Definition term58 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term211 (x0 : nat) (x1 : nat) := int_mul (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term123 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term171 (x0 : nat) := int_mul (int_of_num x0).
Definition term30 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term13 (x0 : nat) := @eq real (real_of_num x0).
Definition term127 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term102 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term216 (x0 : int) := fun y0 : nat => x0 = (int_neg (int_of_num y0)).
Definition term137 (x0 : nat) := ~ ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term4 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term180 (x0 : int) (x1 : int) := or ((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term122 := real_le (real_of_num (NUMERAL 0)).
Definition term152 (x0 : nat) := (fun y0 : real => (real_mul y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term130 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term199 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_of_num x1)).
Definition term45 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term68 (x0 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : nat) := ((~ (~ ((real_of_num x0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))))) -> False) -> ~ ((real_of_num x0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term53 := real_lt (real_of_num (NUMERAL 0)).
Definition term140 (x0 : nat) := real_of_int (int_neg (int_of_num x0)).
Definition term142 (x0 : nat) := @eq real (real_of_int (int_neg (int_of_num x0))).
Definition term197 (x0 : nat) := int_mul (int_neg (int_of_num x0)).
Definition term132 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term24 (x0 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term158 (x0 : int) := (fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) x0.
Definition term10 (x0 : nat) := real_of_int (int_of_num x0).
Definition term118 (x0 : nat) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0)).
Definition term63 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term213 (x0 : nat) (x1 : nat) := int_neg (int_neg (int_of_num (Nat.mul x0 x1))).
Definition term88 (x0 : nat) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term109 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term38 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term32 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term100 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term219 (x0 : int) (x1 : int) := ((exists y0 : nat, x1 = (int_of_num y0)) \/ (exists y0 : nat, x1 = (int_neg (int_of_num y0)))) -> ((exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0)))) -> ((int_mul x0 x1) = (int_of_num (NUMERAL (BIT1 0)))) = (((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0))))) \/ ((x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (x1 = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
Definition term131 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term84 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term191 (x0 : int) := int_neg (int_neg x0).
Definition term93 (x0 : nat) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term77 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term150 (x0 : nat) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) = (real_of_num (NUMERAL 0)).
Definition term73 (x0 : nat) := ((real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0)).
Definition term97 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num x0).
Definition term50 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : nat) := ~ (~ ((int_of_num x0) = (int_neg (int_of_num (NUMERAL (BIT1 0)))))).
Definition term144 (x0 : nat) := ~ (~ ((real_neg (real_of_num x0)) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term21 (x0 : nat) := ~ (~ ((real_of_num x0) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term170 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term174 (x0 : int) (x1 : int) := @eq Prop ((int_mul x0 x1) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term214 (x0 : nat) (x1 : nat) := False \/ ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term178 (x0 : nat) := and (x0 = (NUMERAL (BIT1 0))).
Definition term138 (x0 : nat) := ~ (~ ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term65 (x0 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num x0) (real_of_num (NUMERAL 0))).
Definition term70 (x0 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)).
Definition term81 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term148 (x0 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term220 (x0 : int) := forall y0 : int, ((int_mul x0 y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))) \/ ((x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
Definition term41 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term91 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term190 (x0 : int) := (fun y0 : int => (int_neg (int_neg y0)) = y0) x0.
Definition term85 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term221 := forall y0 : int, forall y1 : int, ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))) \/ ((y0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
Definition term35 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term126 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term59 := S (Nat.add 0 0).
Definition term28 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term78 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term87 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 (x0 : nat) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term196 (x0 : int) (x1 : int) := int_neg (int_mul x0 x1).
Definition term167 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term203 (x0 : nat) := False /\ (x0 = (NUMERAL (BIT1 0))).
Definition term111 := real_mul (real_of_num (NUMERAL 0)).
Definition term176 (x0 : nat) := @eq int (int_of_num x0).
Definition term31 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term147 (x0 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term160 (x0 : int) := exists y0 : nat, x0 = (int_of_num y0).
Definition term33 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term113 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 (x0 : int) := real_neg (real_of_int x0).
Definition term217 (x0 : int) := fun y0 : nat => x0 = (int_of_num y0).
Definition term42 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term95 (x0 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term175 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul x0 x1) = (NUMERAL (BIT1 0))).
Definition term200 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.mul x0 x1)).
Definition term82 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term139 (x0 : nat) := int_neg (int_of_num x0).
Definition term166 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term162 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term11 := real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term204 := int_neg (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term44 (x0 : nat) := real_add (real_of_num x0).
Definition term98 (x0 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term69 (x0 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0).
Definition term184 (x0 : int) (x1 : int) := ((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0))))) \/ ((x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))) /\ (x1 = (int_neg (int_of_num (NUMERAL (BIT1 0)))))).
Definition term92 (x0 : nat) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term209 (x0 : int) (x1 : int) := int_mul x0 (int_neg x1).
Definition term36 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term43 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term19 := real_of_num (NUMERAL (BIT1 0)).
Definition term61 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term212 (x0 : nat) (x1 : nat) := int_neg (int_mul (int_of_num x0) (int_neg (int_of_num x1))).
Definition term117 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term156 (x0 : nat) := ((~ (~ ((real_neg (real_of_num x0)) = (real_of_num (NUMERAL (BIT1 0)))))) -> False) -> ~ ((real_neg (real_of_num x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term153 (x0 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term143 (x0 : nat) := @eq real (real_neg (real_of_num x0)).
Definition term151 (x0 : nat) := forall y0 : real, (real_mul y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) = (real_of_num (NUMERAL 0)).
Definition term74 (x0 : nat) := forall y0 : real, (real_mul y0 (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))))) = (real_of_num (NUMERAL 0)).
Definition term125 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term56 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term71 (x0 : nat) := real_ge (real_of_num x0).
Definition term47 (x0 : nat) := @eq real (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : int) := real_of_int (int_neg x0).
Definition term181 (x0 : nat) (x1 : nat) := or ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term18 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term34 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term182 (x0 : int) := and (x0 = (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term194 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_neg x0) y0) = (int_neg (int_mul x0 y0))) x1.
Definition term161 (x0 : int) := exists y0 : nat, x0 = (int_neg (int_of_num y0)).
Definition term72 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term177 (x0 : int) := and (x0 = (int_of_num (NUMERAL (BIT1 0)))).
Definition term141 (x0 : nat) := real_neg (real_of_int (int_of_num x0)).
Definition term187 (x0 : int) := forall y0 : int, ((int_neg x0) = y0) = (x0 = (int_neg y0)).
Definition term89 (x0 : nat) := @eq real (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term188 (x0 : int) (x1 : int) := (fun y0 : int => ((int_neg x0) = y0) = (x0 = (int_neg y0))) x1.
Definition term172 (x0 : int) (x1 : int) := @eq int (int_mul x0 x1).
Definition term173 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.mul x0 x1)).
Definition term54 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term101 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term51 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term120 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term29 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term164 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term189 (x0 : nat) := (~ ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL (BIT1 0))))) -> ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL (BIT1 0)))) = False.
Definition term165 (x0 : nat) := (~ ((int_of_num x0) = (int_neg (int_of_num (NUMERAL (BIT1 0)))))) -> ((int_of_num x0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) = False.
Definition term202 (x0 : nat) := @eq int (int_neg (int_of_num x0)).
Definition term116 := real_add (real_of_num (NUMERAL 0)).
Definition term155 (x0 : nat) := (~ (~ ((real_neg (real_of_num x0)) = (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term133 (x0 : nat) := (~ (~ ((real_of_num x0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))))) -> False.
Definition term136 (x0 : nat) := ~ (~ (~ ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL (BIT1 0)))))).
Definition term5 (x0 : nat) := ~ (~ (~ ((int_of_num x0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))))).
Definition term94 (x0 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0).
Definition term112 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term17 := int_of_num (NUMERAL (BIT1 0)).
Definition term169 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term3 := NUMERAL (BIT1 0).
Definition term49 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term80 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term46 (x0 : nat) := @eq real (real_sub (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term64 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
