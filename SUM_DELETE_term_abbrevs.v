Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term120 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term91 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term181 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))).
Definition term180 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))).
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := real_sub (@sum a0 x0 x1) (x1 x2).
Definition term147 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term98 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term61 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x0 x1) x2) (real_of_num (NUMERAL 0)).
Definition term15 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) (x1 : real) (x2 : real) := and (~ (x0 = (real_sub x1 x2))).
Definition term196 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term28 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term185 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (x0 (y0 y2) (@iterate a1 a0 x0 (@DELETE a0 y1 y2) y0)) = (@iterate a1 a0 x0 y1 y0).
Definition term100 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term140 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term141 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : nat) := real_neg (real_of_num x0).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := and ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))).
Definition term3 := real_of_num (NUMERAL 0).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := real_add (x2 x1) (@sum a0 (@DELETE a0 x0 x1) x2).
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0)).
Definition term135 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term143 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term162 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term232 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term183 (x0 : real) (x1 : real) (x2 : real) := ((~ ((x1 = (real_sub x2 x0)) = ((real_add x0 x1) = x2))) -> False) -> (x1 = (real_sub x2 x0)) = ((real_add x0 x1) = x2).
Definition term117 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul y0 (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term240 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (@sum a0 (@DELETE a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (y0 y2)).
Definition term186 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (x0 (y0 y2) (@iterate a1 a0 x0 (@DELETE a0 y1 y2) y0)) = (@iterate a1 a0 x0 y1 y0).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term79 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_sub (real_add x0 x1) x2).
Definition term178 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term77 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub x0 (real_sub x1 x2)) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term128 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term218 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@monoidal real real_add) /\ ((@FINITE a0 x1) /\ (@IN a0 x0 x1))) -> (real_add (x2 x0) (@iterate real a0 real_add (@DELETE a0 x1 x0) x2)) = (@iterate real a0 real_add x1 x2).
Definition term177 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := (x1 = (real_sub x2 x0)) /\ (~ ((real_add x0 x1) = x2)).
Definition term84 (x0 : real) (x1 : real) (x2 : real) := or ((x1 = (real_sub x2 x0)) /\ (~ ((real_add x0 x1) = x2))).
Definition term219 := and (@monoidal real real_add).
Definition term155 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))).
Definition term231 (a0 : Type') := forall y0 : a0, True.
Definition term179 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_sub x0 (real_sub x1 x2)).
Definition term133 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term132 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term242 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term237 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term95 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term210 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> ((@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = x3) -> (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> (@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> x3).
Definition term164 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term139 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term16 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @sum a0 (@DELETE a0 x0 x1) x2.
Definition term38 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term101 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term12 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term149 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) = y0) -> (y0 -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = y1) -> (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = (y0 -> y1)) x3.
Definition term173 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term20 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term131 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term193 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@IN a0 x0 x1).
Definition term221 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@monoidal real real_add) /\ ((@FINITE a0 x1) /\ (@IN a0 x0 x1)).
Definition term170 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul y0 (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term57 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_add x0 x1) x2)) (real_of_num (NUMERAL 0)).
Definition term209 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) = ((@FINITE a0 x2) /\ (@IN a0 x1 x2))) -> (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> ((@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = x3) -> (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> (@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> x3).
Definition term96 := real_lt (real_of_num (NUMERAL 0)).
Definition term174 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term87 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0)))).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term199 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))).
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_neg (real_sub x0 (real_sub x1 x2))).
Definition term216 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := real_add (x2 x1) (@iterate real a0 real_add (@DELETE a0 x0 x1) x2).
Definition term106 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term142 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term29 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term22 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = True.
Definition term129 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term71 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_sub x0 (real_sub x1 x2)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_sub x1 x2))) (real_of_num (NUMERAL 0))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = (real_sub x2 x0))) /\ ((real_add x0 x1) = x2).
Definition term163 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term111 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term227 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (@IN a0 x0 x1)) -> True.
Definition term189 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (x0 (x1 y1) (@iterate a1 a0 x0 (@DELETE a0 y0 y1) x1)) = (@iterate a1 a0 x0 y0 x1)) x2.
Definition term115 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) = (real_of_num (NUMERAL 0)).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term93 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term53 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) (x4 : Prop) := (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = x4) -> (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = (x3 -> x4).
Definition term233 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1)).
Definition term225 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> ((@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = True) -> (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> (@sum a0 (@DELETE a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (x0 x1))) = (((@FINITE a0 x2) /\ (@IN a0 x1 x2)) -> True).
Definition term157 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term159 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_sub (real_add x0 x1) x2).
Definition term229 (a0 : Type') := fun y0 : a0 => True.
Definition term37 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term176 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_sub (real_add x0 x1) x2) (real_of_num (NUMERAL 0))).
Definition term136 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term126 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term35 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term32 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term215 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (x0 x1).
Definition term81 (x0 : real) (x1 : real) (x2 : real) := and ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub x0 (real_sub x1 x2)).
Definition term88 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) \/ (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))).
Definition term113 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))).
Definition term191 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (fun y0 : a0 => ((@FINITE a0 x1) /\ (@IN a0 y0 x1)) -> (x0 (x2 y0) (@iterate a1 a0 x0 (@DELETE a0 x1 y0) x2)) = (@iterate a1 a0 x0 x1 x2)) x3.
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@DELETE a0 x0 x1).
Definition term26 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term195 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@monoidal a1 x1) -> ((@FINITE a0 x2) /\ (@IN a0 x0 x2)) -> (x1 (x3 x0) (@iterate a1 a0 x1 (@DELETE a0 x2 x0) x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term161 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term103 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_sub (real_add x0 x1) x2) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add x0 x1) x2)) (real_of_num (NUMERAL 0))).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term102 := S (Nat.add 0 0).
Definition term18 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term127 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term66 (x0 : real) (x1 : real) (x2 : real) := and (x0 = (real_sub x1 x2)).
Definition term11 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term138 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add x0 x1) x2.
Definition term238 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (@sum a0 (@DELETE a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (y0 y2)).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_add x0 x1) x2)).
Definition term152 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term206 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) := forall y0 : Prop, (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = y0) -> (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = (x3 -> y0).
Definition term200 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term89 (x0 : real) (x1 : real) (x2 : real) := or ((((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) \/ (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))))).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := ((x1 = (real_sub x2 x0)) /\ (~ ((real_add x0 x1) = x2))) \/ ((~ (x1 = (real_sub x2 x0))) /\ ((real_add x0 x1) = x2)).
Definition term234 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term59 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x0 x1) x2).
Definition term239 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term217 (a0 : Type') (x0 : a0) (x1 : type1627) (x2 : a0 -> Prop) (x3 : a0 -> real) := ((@monoidal real x1) /\ ((@FINITE a0 x2) /\ (@IN a0 x0 x2))) -> (x1 (x3 x0) (@iterate real a0 x1 (@DELETE a0 x2 x0) x3)) = (@iterate real a0 x1 x2 x3).
Definition term198 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x1) /\ ((@FINITE a0 x2) /\ (@IN a0 x0 x2))) -> (x1 (x3 x0) (@iterate a1 a0 x1 (@DELETE a0 x2 x0) x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term197 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term144 := real_mul (real_of_num (NUMERAL 0)).
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) = y0) -> (y0 -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = y1) -> (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = (y0 -> y1).
Definition term201 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term158 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term171 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))).
Definition term187 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (x0 (y0 y2) (@iterate a1 a0 x0 (@DELETE a0 y1 y2) y0)) = (@iterate a1 a0 x0 y1 y0)) x1.
Definition term40 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_sub x0 (real_sub x1 x2)).
Definition term21 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term31 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term24 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term194 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> a1) := x0 (x3 x2) (@iterate a1 a0 x0 (@DELETE a0 x1 x2) x3).
Definition term36 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term146 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term207 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) = x3) -> (x3 -> ((@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = y0) -> (((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2))) = (x3 -> y0)) x4.
Definition term33 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := ~ (x0 = (real_sub x1 x2)).
Definition term83 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))).
Definition term78 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_sub x0 (real_sub x1 x2)) (real_of_num (NUMERAL 0))).
Definition term56 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term190 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, ((@FINITE a0 x1) /\ (@IN a0 y0 x1)) -> (x0 (x2 y0) (@iterate a1 a0 x0 (@DELETE a0 x1 y0) x2)) = (@iterate a1 a0 x0 x1 x2).
Definition term137 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term30 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term75 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub x0 (real_sub x1 x2))) (real_of_num (NUMERAL 0)).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @eq real (real_add (x2 x1) (@sum a0 (@DELETE a0 x0 x1) x2)).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := real_sub x0 (real_sub x1 x2).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 x1) = x2).
Definition term74 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub x0 (real_sub x1 x2))).
Definition term27 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := or (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))))).
Definition term34 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term105 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term23 := real_of_num (NUMERAL (BIT1 0)).
Definition term104 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))).
Definition term148 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term7 (x0 : real) (x1 : real) (x2 : real) := real_sub x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term13 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term192 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@FINITE a0 x2) /\ (@IN a0 x0 x2)) -> (x1 (x3 x0) (@iterate a1 a0 x1 (@DELETE a0 x2 x0) x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term116 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, (real_mul y0 (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) = (real_of_num (NUMERAL 0)).
Definition term160 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term99 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term226 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term175 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@iterate real a0 real_add x0 x1).
Definition term25 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @iterate real a0 real_add (@DELETE a0 x0 x1).
Definition term184 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, forall y3 : a0, ((@FINITE a0 y2) /\ (@IN a0 y3 y2)) -> (y0 (y1 y3) (@iterate a1 a0 y0 (@DELETE a0 y2 y3) y1)) = (@iterate a1 a0 y0 y2 y1)) x0.
Definition term182 (x0 : real) (x1 : real) (x2 : real) := (~ ((x1 = (real_sub x2 x0)) = ((real_add x0 x1) = x2))) -> False.
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @iterate real a0 real_add (@DELETE a0 x0 x1) x2.
Definition term154 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ~ ((x1 = (real_sub x2 x0)) = ((real_add x0 x1) = x2)).
Definition term114 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2).
Definition term50 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term4 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term112 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term97 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term130 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term94 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)).
Definition term19 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term172 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term110 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term169 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))).
Definition term90 (x0 : real) (x1 : real) (x2 : real) := ((((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) \/ (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))))).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_neg (real_sub (real_add x0 x1) x2)).
Definition term150 := real_add (real_of_num (NUMERAL 0)).
Definition term151 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term235 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1)).
Definition term188 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (x0 (x1 y1) (@iterate a1 a0 x0 (@DELETE a0 y0 y1) x1)) = (@iterate a1 a0 x0 y0 x1).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term86 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) /\ ((real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) = (real_of_num (NUMERAL 0)))).
Definition term145 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term51 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term17 := NUMERAL (BIT1 0).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term121 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term109 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term153 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term92 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term241 (a0 : Type') := forall y0 : a0 -> real, True.
Definition term236 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term107 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term156 := real_gt (real_of_num (NUMERAL 0)).
