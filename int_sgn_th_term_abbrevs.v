Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term128 (x0 : real) := (integer x0) \/ ((forall y0 : nat, ~ (x0 = (real_of_num y0))) /\ (forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0))))).
Definition term57 (x0 : int) := @eq Prop (integer (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term309 := (((~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term290 := (((~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term63 := (((~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term2 (x0 : real) := (fun y0 : real => (real_sgn y0) = (@COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) x0.
Definition term295 := (~ ((real_neg (real_of_num (NUMERAL (BIT1 0)))) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (real_neg (real_of_num (NUMERAL (BIT1 0)))) = (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term243 (x0 : real) := (integer x0) \/ (forall y0 : nat, (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0))))).
Definition term284 := (~ False) -> False.
Definition term311 := imp (~ (integer (real_of_num (NUMERAL 0)))).
Definition term101 := imp (~ (integer (real_of_num (NUMERAL (BIT1 0))))).
Definition term244 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term191 (x0 : real) := fun y0 : nat => (fun y1 : real => fun y2 : nat => (~ (integer y1)) \/ ((y1 = (real_of_num y2)) \/ (y1 = (real_neg (real_of_num y2))))) x0 y0.
Definition term193 := fun y0 : real => exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (integer y2)) \/ ((y2 = (real_of_num y3)) \/ (y2 = (real_neg (real_of_num y3))))) y0 y1.
Definition term4 (x0 : int) := (fun y0 : int => (int_sgn y0) = (int_of_real (real_sgn (real_of_int y0)))) x0.
Definition term34 (x0 : int) := and ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => integer y0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term235 (x0 : real) := @eq Prop ((forall y0 : nat, ~ (x0 = (real_of_num y0))) /\ (forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0))))).
Definition term234 (x0 : real) := @eq Prop ((forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0)).
Definition term179 := fun y0 : real => exists y1 : nat, (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1)))).
Definition term76 (x0 : real) (x1 : nat) := or ((fun y0 : nat => x0 = (real_of_num y0)) x1).
Definition term226 (x0 : real) := forall y0 : nat, ((fun y1 : nat => ~ (x0 = (real_of_num y1))) y0) /\ ((fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term233 (x0 : real) := forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0.
Definition term229 (x0 : real) := forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0.
Definition term6 (x0 : int) := real_sgn (real_of_int x0).
Definition term79 (x0 : nat) := real_neg (real_of_num x0).
Definition term12 (x0 : int) := @eq real (real_of_int (int_of_real (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term238 (x0 : real) (x1 : nat) := ((fun y0 : nat => ~ (x0 = (real_of_num y0))) x1) /\ ((fun y0 : nat => ~ (x0 = (real_neg (real_of_num y0)))) x1).
Definition term166 (x0 : real) := (~ (integer x0)) \/ (exists y0 : nat, (fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term275 (x0 : Prop) := ~ (~ x0).
Definition term42 := real_of_num (NUMERAL 0).
Definition term305 := (~ (integer (real_of_num (NUMERAL 0)))) -> False.
Definition term286 := (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term59 := (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term73 (x0 : real) := fun y0 : nat => x0 = (real_of_num y0).
Definition term37 (x0 : int) := @eq Prop ((fun y0 : real => integer y0) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term220 := fun y0 : real -> nat => (forall y1 : real, (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) /\ ((fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0).
Definition term227 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (x0 = (real_of_num y0))) x1.
Definition term192 (x0 : real) := exists y0 : nat, (fun y1 : real => fun y2 : nat => (~ (integer y1)) \/ ((y1 = (real_of_num y2)) \/ (y1 = (real_neg (real_of_num y2))))) x0 y0.
Definition term154 := and (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))).
Definition term119 (x0 : real) := and (~ (exists y0 : nat, x0 = (real_of_num y0))).
Definition term91 (x0 : real) := or (exists y0 : nat, x0 = (real_of_num y0)).
Definition term41 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term297 (x0 : nat) (x1 : real) := (~ (~ (x1 = (real_neg (real_of_num x0))))) -> integer x1.
Definition term274 (x0 : nat) (x1 : real) := (~ (~ (x1 = (real_of_num x0)))) -> integer x1.
Definition term152 := forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1))))).
Definition term108 (x0 : real) (x1 : nat) := ~ (x0 = (real_of_num x1)).
Definition term95 (x0 : real) := (exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term8 (x0 : int) := int_of_real (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term45 (x0 : int) := imp (~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term245 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term265 := fun y0 : real => forall y1 : nat, ((integer y0) \/ (~ (y0 = (real_of_num y1)))) /\ ((integer y0) \/ (~ (y0 = (real_neg (real_of_num y1))))).
Definition term260 := fun y0 : real => forall y1 : nat, (integer y0) \/ ((~ (y0 = (real_of_num y1))) /\ (~ (y0 = (real_neg (real_of_num y1))))).
Definition term169 (x0 : real) (x1 : nat) := (fun y0 : nat => (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))) x1.
Definition term153 := and (forall y0 : real, (fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0).
Definition term208 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term58 (x0 : Prop) := (~ x0) -> False.
Definition term271 := ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term225 (x0 : real) := (forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term100 := ~ (forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term66 := ~ (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))).
Definition term30 := integer (real_of_num (NUMERAL (BIT1 0))).
Definition term56 (x0 : int) := @eq Prop ((fun y0 : real => integer y0) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term161 (x0 : real) := (~ (integer x0)) \/ (exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))).
Definition term25 (x0 : int) := integer (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term129 (x0 : real) := and ((integer x0) \/ (~ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))))).
Definition term18 := fun y0 : real => integer y0.
Definition term28 (x0 : int) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0))) -> integer (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term75 (x0 : real) (x1 : nat) := (fun y0 : nat => x0 = (real_of_num y0)) x1.
Definition term252 (x0 : real) := forall y0 : nat, (fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0.
Definition term122 (x0 : real) := (forall y0 : nat, ~ (x0 = (real_of_num y0))) /\ (forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0)))).
Definition term209 (x0 : Prop) (x1 : type1024) := x0 /\ (exists y0 : real -> nat, x1 y0).
Definition term165 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term270 := (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : real) := @COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term214 := fun y0 : real -> nat => (fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0.
Definition term189 (x0 : real) (x1 : nat) := (fun y0 : real => fun y1 : nat => (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) x0 x1.
Definition term273 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term224 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term140 := (forall y0 : real, (fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0).
Definition term222 := exists y0 : real -> nat, (forall y1 : real, (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) /\ (forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1)))))).
Definition term207 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term120 (x0 : real) := and (forall y0 : nat, ~ (x0 = (real_of_num y0))).
Definition term31 (x0 : int) := imp (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term272 (x0 : Prop) := (~ x0) -> x0.
Definition term301 (x0 : nat) (x1 : real) := (x1 = (real_neg (real_of_num x0))) -> integer x1.
Definition term48 := (fun y0 : real => integer y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term127 (x0 : real) := (integer x0) \/ (~ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0))))).
Definition term1 (x0 : real) := real_of_int (int_of_real x0).
Definition term94 (x0 : real) := exists y0 : nat, x0 = (real_neg (real_of_num y0)).
Definition term168 (x0 : real) := ~ (integer x0).
Definition term282 := (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> integer (real_of_num (NUMERAL (BIT1 0))).
Definition term181 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term199 (x0 : real -> nat) := fun y0 : real => (fun y1 : real => fun y2 : nat => (~ (integer y1)) \/ ((y1 = (real_of_num y2)) \/ (y1 = (real_neg (real_of_num y2))))) y0 (x0 y0).
Definition term206 := (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (exists y0 : real -> nat, forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1)))))).
Definition term299 (x0 : real) (x1 : nat) := imp (~ (~ (x0 = (real_neg (real_of_num x1))))).
Definition term239 (x0 : real) (x1 : nat) := (~ (x0 = (real_of_num x1))) /\ (~ (x0 = (real_neg (real_of_num x1)))).
Definition term266 := forall y0 : real, forall y1 : nat, ((integer y0) \/ (~ (y0 = (real_of_num y1)))) /\ ((integer y0) \/ (~ (y0 = (real_neg (real_of_num y1))))).
Definition term261 := forall y0 : real, forall y1 : nat, (integer y0) \/ ((~ (y0 = (real_of_num y1))) /\ (~ (y0 = (real_neg (real_of_num y1))))).
Definition term205 := exists y0 : real -> nat, forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1))))).
Definition term186 := exists y0 : real -> nat, forall y1 : real, (fun y2 : real => fun y3 : nat => (~ (integer y2)) \/ ((y2 = (real_of_num y3)) \/ (y2 = (real_neg (real_of_num y3))))) y1 (y0 y1).
Definition term184 (x0 : type1622) := exists y0 : real -> nat, forall y1 : real, x0 y1 (y0 y1).
Definition term294 (x0 : real) (x1 : nat) := (integer x0) \/ (~ (x0 = (real_neg (real_of_num x1)))).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term0 := forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1)))).
Definition term246 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (forall y0 : nat, x1 y0).
Definition term11 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term196 (x0 : real -> nat) (x1 : real) := (fun y0 : real => fun y1 : nat => (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) x1 (x0 x1).
Definition term5 (x0 : int) := int_of_real (real_sgn (real_of_int x0)).
Definition term210 (x0 : Prop) (x1 : type1024) := exists y0 : real -> nat, x0 /\ (x1 y0).
Definition term190 (x0 : real) (x1 : nat) := (fun y0 : nat => (~ (integer x0)) \/ ((x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))))) x1.
Definition term23 (x0 : int) := @COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term155 := fun y0 : real => (fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0.
Definition term150 := fun y0 : real => (fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0.
Definition term213 (x0 : real -> nat) := (fun y0 : real -> nat => forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1)))))) x0.
Definition term15 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term39 (x0 : int) := ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> (fun y0 : real => integer y0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) /\ ((~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0)))) -> (fun y0 : real => integer y0) (real_of_num (NUMERAL 0))).
Definition term249 (x0 : real) := forall y0 : nat, (integer x0) \/ ((fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0).
Definition term241 (x0 : real) := fun y0 : nat => (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0)))).
Definition term202 (x0 : real -> nat) := forall y0 : real, (~ (integer y0)) \/ ((y0 = (real_of_num (x0 y0))) \/ (y0 = (real_neg (real_of_num (x0 y0))))).
Definition term86 (x0 : real) := @eq Prop (exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))).
Definition term85 (x0 : real) := @eq Prop (exists y0 : nat, ((fun y1 : nat => x0 = (real_of_num y1)) y0) \/ ((fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0)).
Definition term111 (x0 : real) := forall y0 : nat, ~ (x0 = (real_of_num y0)).
Definition term13 (x0 : int) := integer (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term306 := ~ (integer (real_of_num (NUMERAL 0))).
Definition term263 (x0 : real) := fun y0 : nat => ((integer x0) \/ (~ (x0 = (real_of_num y0)))) /\ ((integer x0) \/ (~ (x0 = (real_neg (real_of_num y0))))).
Definition term242 (x0 : real) := forall y0 : nat, (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0)))).
Definition term149 := @eq Prop (forall y0 : real, ((integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ ((~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1)))))).
Definition term148 := @eq Prop (forall y0 : real, ((fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0)).
Definition term255 (x0 : real) (x1 : nat) := (integer x0) \/ ((fun y0 : nat => (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0))))) x1).
Definition term304 := (integer (real_neg (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term77 (x0 : real) (x1 : nat) := or (x0 = (real_of_num x1)).
Definition term27 (x0 : int) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (fun y0 : real => integer y0) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term267 (x0 : real) := (fun y0 : real => forall y1 : nat, ((integer y0) \/ (~ (y0 = (real_of_num y1)))) /\ ((integer y0) \/ (~ (y0 = (real_neg (real_of_num y1)))))) x0.
Definition term115 (x0 : real) (x1 : nat) := ~ (x0 = (real_neg (real_of_num x1))).
Definition term201 (x0 : real -> nat) := forall y0 : real, (fun y1 : real => fun y2 : nat => (~ (integer y1)) \/ ((y1 = (real_of_num y2)) \/ (y1 = (real_neg (real_of_num y2))))) y0 (x0 y0).
Definition term72 (x0 : real) := (exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0).
Definition term89 (x0 : real) := exists y0 : nat, x0 = (real_of_num y0).
Definition term251 (x0 : real) := fun y0 : nat => (fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0.
Definition term215 := exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0.
Definition term237 (x0 : real) (x1 : nat) := and (~ (x0 = (real_of_num x1))).
Definition term51 (x0 : int) := (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> (fun y0 : real => integer y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term131 (x0 : real) := ((integer x0) \/ (~ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))))) /\ ((~ (integer x0)) \/ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0))))).
Definition term36 (x0 : int) := ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> integer (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0))) -> integer (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term173 (x0 : real) := @eq Prop ((~ (integer x0)) \/ (exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))))).
Definition term172 (x0 : real) := @eq Prop ((~ (integer x0)) \/ (exists y0 : nat, (fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0)).
Definition term60 := ~ (integer (real_of_num (NUMERAL (BIT1 0)))).
Definition term98 := fun y0 : real => (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1)))).
Definition term19 (x0 : int) := (fun y0 : real => integer y0) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term10 (x0 : int) := real_of_int (int_of_real (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term195 := @eq Prop (forall y0 : real, exists y1 : nat, (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))).
Definition term194 := @eq Prop (forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (integer y2)) \/ ((y2 = (real_of_num y3)) \/ (y2 = (real_neg (real_of_num y3))))) y0 y1).
Definition term307 := (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term288 := (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term61 := (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term163 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term81 (x0 : real) (x1 : nat) := (x0 = (real_of_num x1)) \/ (x0 = (real_neg (real_of_num x1))).
Definition term170 (x0 : real) := fun y0 : nat => (fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0.
Definition term144 (x0 : real) := and ((fun y0 : real => (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) x0).
Definition term118 (x0 : real) := forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0))).
Definition term219 (x0 : real -> nat) := (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (forall y0 : real, (~ (integer y0)) \/ ((y0 = (real_of_num (x0 y0))) \/ (y0 = (real_neg (real_of_num (x0 y0)))))).
Definition term158 := (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (forall y0 : real, (~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term83 (x0 : real) := fun y0 : nat => (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term211 := (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0).
Definition term236 (x0 : real) (x1 : nat) := and ((fun y0 : nat => ~ (x0 = (real_of_num y0))) x1).
Definition term313 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term54 (x0 : int) := and ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> integer (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term162 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term279 (x0 : nat) (x1 : real) := (x1 = (real_of_num x0)) -> integer x1.
Definition term50 (x0 : int) := imp (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term277 (x0 : real) (x1 : nat) := imp (~ (~ (x0 = (real_of_num x1)))).
Definition term218 (x0 : real -> nat) := (forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ ((fun y0 : real -> nat => forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1)))))) x0).
Definition term103 (x0 : nat -> Prop) := ~ (ex x0).
Definition term197 (x0 : real -> nat) (x1 : real) := (fun y0 : nat => (~ (integer x1)) \/ ((x1 = (real_of_num y0)) \/ (x1 = (real_neg (real_of_num y0))))) (x0 x1).
Definition term167 (x0 : real) := exists y0 : nat, (~ (integer x0)) \/ ((fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term146 (x0 : real) := ((fun y0 : real => (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) x0) /\ ((fun y0 : real => (~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))) x0).
Definition term71 (x0 : real) := exists y0 : nat, ((fun y1 : nat => x0 = (real_of_num y1)) y0) \/ ((fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0).
Definition term185 := forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (integer y2)) \/ ((y2 = (real_of_num y3)) \/ (y2 = (real_neg (real_of_num y3))))) y0 y1.
Definition term183 (x0 : type1622) := forall y0 : real, exists y1 : nat, x0 y0 y1.
Definition term180 := forall y0 : real, exists y1 : nat, (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1)))).
Definition term117 (x0 : real) := fun y0 : nat => ~ (x0 = (real_neg (real_of_num y0))).
Definition term175 (x0 : real) (x1 : nat) := (~ (integer x0)) \/ ((x0 = (real_of_num x1)) \/ (x0 = (real_neg (real_of_num x1)))).
Definition term124 (x0 : real) := or (~ (integer x0)).
Definition term316 := (~ (integer (real_of_num (NUMERAL 0)))) -> integer (real_of_num (NUMERAL 0)).
Definition term52 (x0 : int) := (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> integer (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term137 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term285 := (forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))) -> False.
Definition term65 := (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term20 (x0 : int) := ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => integer y0) (real_of_num (NUMERAL (BIT1 0)))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (fun y0 : real => integer y0) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term198 (x0 : real -> nat) (x1 : real) := (~ (integer x1)) \/ ((x1 = (real_of_num (x0 x1))) \/ (x1 = (real_neg (real_of_num (x0 x1))))).
Definition term104 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term130 (x0 : real) := and ((integer x0) \/ ((forall y0 : nat, ~ (x0 = (real_of_num y0))) /\ (forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0)))))).
Definition term142 := fun y0 : real => (~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1)))).
Definition term188 (x0 : real) := (fun y0 : real => fun y1 : nat => (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) x0.
Definition term303 := (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> integer (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term302 := ((real_neg (real_of_num (NUMERAL (BIT1 0)))) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) -> integer (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 (x0 : real) (x1 : nat) := imp (x0 = (real_neg (real_of_num x1))).
Definition term141 := fun y0 : real => (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1))))).
Definition term40 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term315 := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) -> integer (real_of_num (NUMERAL 0)).
Definition term156 := forall y0 : real, (fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0.
Definition term151 := forall y0 : real, (fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0.
Definition term278 (x0 : real) (x1 : nat) := imp (x0 = (real_of_num x1)).
Definition term312 := (~ (integer (real_of_num (NUMERAL 0)))) -> ~ (forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term293 := (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> ~ (forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term102 := (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> ~ (forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term35 (x0 : int) := and ((real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> integer (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 (x0 : int) := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term9 (x0 : int) := real_of_int (int_sgn x0).
Definition term223 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term143 (x0 : real) := (fun y0 : real => (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) x0.
Definition term171 (x0 : real) := exists y0 : nat, (fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0.
Definition term93 (x0 : real) := exists y0 : nat, (fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0.
Definition term88 (x0 : real) := exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0.
Definition term43 := (fun y0 : real => integer y0) (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => integer y0) x0) /\ ((~ x1) -> (fun y0 : real => integer y0) x2).
Definition term283 := (integer (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term296 := ~ ((real_neg (real_of_num (NUMERAL (BIT1 0)))) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term258 (x0 : real) := fun y0 : nat => (integer x0) \/ ((~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0))))).
Definition term280 := ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL (BIT1 0)))) -> integer (real_of_num (NUMERAL (BIT1 0))).
Definition term212 := exists y0 : real -> nat, (forall y1 : real, (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) /\ ((fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0).
Definition term132 (x0 : real) := ((integer x0) \/ ((forall y0 : nat, ~ (x0 = (real_of_num y0))) /\ (forall y0 : nat, ~ (x0 = (real_neg (real_of_num y0)))))) /\ ((~ (integer x0)) \/ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0))))).
Definition term319 (x0 : int) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term22 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term44 := integer (real_of_num (NUMERAL 0)).
Definition term221 := fun y0 : real -> nat => (forall y1 : real, (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) /\ (forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1)))))).
Definition term256 (x0 : real) (x1 : nat) := (integer x0) \/ ((~ (x0 = (real_of_num x1))) /\ (~ (x0 = (real_neg (real_of_num x1))))).
Definition term317 := (integer (real_of_num (NUMERAL 0))) -> False.
Definition term113 (x0 : real) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0).
Definition term106 (x0 : real) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term157 := forall y0 : real, (~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1)))).
Definition term46 (x0 : int) := (~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0)))) -> (fun y0 : real => integer y0) (real_of_num (NUMERAL 0)).
Definition term204 := fun y0 : real -> nat => forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1))))).
Definition term203 := fun y0 : real -> nat => forall y1 : real, (fun y2 : real => fun y3 : nat => (~ (integer y2)) \/ ((y2 = (real_of_num y3)) \/ (y2 = (real_neg (real_of_num y3))))) y1 (y0 y1).
Definition term126 (x0 : real) := or (integer x0).
Definition term29 := (fun y0 : real => integer y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term123 (x0 : real) := ~ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))).
Definition term55 (x0 : int) := ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> integer (real_neg (real_of_num (NUMERAL (BIT1 0))))) /\ ((~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0)))) -> integer (real_of_num (NUMERAL 0))).
Definition term250 (x0 : real) (x1 : nat) := (fun y0 : nat => (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0))))) x1.
Definition term16 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => integer y0) (@COND real x0 x1 x2).
Definition term49 := integer (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term320 := forall y0 : int, (real_of_int (int_sgn y0)) = (real_sgn (real_of_int y0)).
Definition term200 (x0 : real -> nat) := fun y0 : real => (~ (integer y0)) \/ ((y0 = (real_of_num (x0 y0))) \/ (y0 = (real_neg (real_of_num (x0 y0))))).
Definition term308 := ((~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term289 := ((~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term62 := ((~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term298 (x0 : real) (x1 : nat) := ~ (~ (x0 = (real_neg (real_of_num x1)))).
Definition term110 (x0 : real) := fun y0 : nat => ~ (x0 = (real_of_num y0)).
Definition term176 (x0 : real) := fun y0 : nat => (~ (integer x0)) \/ ((fun y1 : nat => (x0 = (real_of_num y1)) \/ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term21 := real_of_num (NUMERAL (BIT1 0)).
Definition term231 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (x0 = (real_neg (real_of_num y0)))) x1.
Definition term14 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term276 (x0 : real) (x1 : nat) := ~ (~ (x0 = (real_of_num x1))).
Definition term292 := imp (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term247 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 \/ (x1 y0).
Definition term230 (x0 : real) := and (forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0).
Definition term264 (x0 : real) := forall y0 : nat, ((integer x0) \/ (~ (x0 = (real_of_num y0)))) /\ ((integer x0) \/ (~ (x0 = (real_neg (real_of_num y0))))).
Definition term97 := fun y0 : real => (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1)))).
Definition term147 := fun y0 : real => ((fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0).
Definition term257 (x0 : real) := fun y0 : nat => (integer x0) \/ ((fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0).
Definition term268 (x0 : real) (x1 : nat) := (fun y0 : nat => ((integer x0) \/ (~ (x0 = (real_of_num y0)))) /\ ((integer x0) \/ (~ (x0 = (real_neg (real_of_num y0)))))) x1.
Definition term134 := forall y0 : real, ((integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ ((~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term232 (x0 : real) := fun y0 : nat => (fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0.
Definition term228 (x0 : real) := fun y0 : nat => (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0.
Definition term145 (x0 : real) := (fun y0 : real => (~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))) x0.
Definition term78 (x0 : real) (x1 : nat) := (fun y0 : nat => x0 = (real_neg (real_of_num y0))) x1.
Definition term138 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term133 := fun y0 : real => ((integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ ((~ (integer y0)) \/ ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1))))).
Definition term99 := forall y0 : real, (integer y0) = ((exists y1 : nat, y0 = (real_of_num y1)) \/ (exists y1 : nat, y0 = (real_neg (real_of_num y1)))).
Definition term38 (x0 : int) := @eq Prop (integer (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term84 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term217 := @eq Prop ((forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (exists y0 : real -> nat, forall y1 : real, (~ (integer y1)) \/ ((y1 = (real_of_num (y0 y1))) \/ (y1 = (real_neg (real_of_num (y0 y1))))))).
Definition term216 := @eq Prop ((forall y0 : real, (integer y0) \/ ((forall y1 : nat, ~ (y0 = (real_of_num y1))) /\ (forall y1 : nat, ~ (y0 = (real_neg (real_of_num y1)))))) /\ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (integer y2)) \/ ((y2 = (real_of_num (y1 y2))) \/ (y2 = (real_neg (real_of_num (y1 y2)))))) y0)).
Definition term177 (x0 : real) := fun y0 : nat => (~ (integer x0)) \/ ((x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term69 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term287 := ~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term116 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0).
Definition term109 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term259 (x0 : real) := forall y0 : nat, (integer x0) \/ ((~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0))))).
Definition term114 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => x0 = (real_neg (real_of_num y0))) x1).
Definition term107 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => x0 = (real_of_num y0)) x1).
Definition term47 (x0 : int) := (~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0)))) -> integer (real_of_num (NUMERAL 0)).
Definition term32 (x0 : int) := (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => integer y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term92 (x0 : real) := fun y0 : nat => (fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0.
Definition term240 (x0 : real) := fun y0 : nat => ((fun y1 : nat => ~ (x0 = (real_of_num y1))) y0) /\ ((fun y1 : nat => ~ (x0 = (real_neg (real_of_num y1)))) y0).
Definition term121 (x0 : real) := (~ (exists y0 : nat, x0 = (real_of_num y0))) /\ (~ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))).
Definition term248 (x0 : real) := (integer x0) \/ (forall y0 : nat, (fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0).
Definition term269 (x0 : real) (x1 : nat) := (integer x0) \/ (~ (x0 = (real_of_num x1))).
Definition term82 (x0 : real) := fun y0 : nat => ((fun y1 : nat => x0 = (real_of_num y1)) y0) \/ ((fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0).
Definition term90 (x0 : real) := or (exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term262 (x0 : real) (x1 : nat) := ((integer x0) \/ (~ (x0 = (real_of_num x1)))) /\ ((integer x0) \/ (~ (x0 = (real_neg (real_of_num x1))))).
Definition term310 := (((~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> ((~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term291 := (((~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> ((~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_neg (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term64 := (((~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> ((~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False) -> (~ (integer (real_of_num (NUMERAL (BIT1 0))))) -> (forall y0 : real, (integer y0) = (exists y1 : nat, (y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1))))) -> False.
Definition term33 (x0 : int) := (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) -> integer (real_of_num (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) (x1 : nat) := ((fun y0 : nat => x0 = (real_of_num y0)) x1) \/ ((fun y0 : nat => x0 = (real_neg (real_of_num y0))) x1).
Definition term74 (x0 : real) := fun y0 : nat => x0 = (real_neg (real_of_num y0)).
Definition term182 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term178 (x0 : real) := exists y0 : nat, (~ (integer x0)) \/ ((x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))).
Definition term96 (x0 : real) := @eq Prop (integer x0).
Definition term26 (x0 : int) := imp (~ (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0))).
Definition term254 (x0 : real) := @eq Prop ((integer x0) \/ (forall y0 : nat, (~ (x0 = (real_of_num y0))) /\ (~ (x0 = (real_neg (real_of_num y0)))))).
Definition term253 (x0 : real) := @eq Prop ((integer x0) \/ (forall y0 : nat, (fun y1 : nat => (~ (x0 = (real_of_num y1))) /\ (~ (x0 = (real_neg (real_of_num y1))))) y0)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term24 (x0 : int) := (fun y0 : real => integer y0) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term164 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term139 := forall y0 : real, ((fun y1 : real => (integer y1) \/ ((forall y2 : nat, ~ (y1 = (real_of_num y2))) /\ (forall y2 : nat, ~ (y1 = (real_neg (real_of_num y2)))))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((exists y2 : nat, y1 = (real_of_num y2)) \/ (exists y2 : nat, y1 = (real_neg (real_of_num y2))))) y0).
Definition term87 (x0 : real) := fun y0 : nat => (fun y1 : nat => x0 = (real_of_num y1)) y0.
Definition term112 (x0 : real) := ~ (exists y0 : nat, x0 = (real_neg (real_of_num y0))).
Definition term105 (x0 : real) := ~ (exists y0 : nat, x0 = (real_of_num y0)).
Definition term125 (x0 : real) := (~ (integer x0)) \/ ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))).
Definition term281 := NUMERAL (BIT1 0).
Definition term70 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term53 (x0 : int) := and ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> (fun y0 : real => integer y0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term174 (x0 : real) (x1 : nat) := (~ (integer x0)) \/ ((fun y0 : nat => (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0)))) x1).
Definition term314 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term318 (x0 : int) := ~ (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term187 := fun y0 : real => fun y1 : nat => (~ (integer y0)) \/ ((y0 = (real_of_num y1)) \/ (y0 = (real_neg (real_of_num y1)))).
Definition term160 (x0 : real) := @eq Prop ((exists y0 : nat, x0 = (real_of_num y0)) \/ (exists y0 : nat, x0 = (real_neg (real_of_num y0)))).
Definition term159 (x0 : real) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 = (real_neg (real_of_num y1))) y0)).
