Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => @COND real (x1 y0) (x2 y0) (x3 y0)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := real_sub (@sum a0 x0 x1) (x1 x2).
Definition term283 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := real_add (@sum a0 x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x1 x2)).
Definition term221 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term87 := (~ False) -> False.
Definition term234 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (y3 = y1))) y3)) = (@DELETE a0 y0 y1)) x0.
Definition term0 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1)) x0.
Definition term250 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (x3 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x2 x3)))).
Definition term206 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3)).
Definition term312 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := or (real_gt (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))) (real_of_num (NUMERAL 0))).
Definition term262 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term208 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_sub (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))).
Definition term273 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term274 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term220 (x0 : nat) := real_neg (real_of_num x0).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y2 = x1)) y2))) = (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term51 (x0 : Prop) := ~ (~ x0).
Definition term261 := real_of_num (NUMERAL 0).
Definition term310 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_gt (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (x1 = x2).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (y0 = x2)) x3).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (x3 = x2)) x3.
Definition term90 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, ((y1 y2) /\ (y2 = y0)) = (y2 = y0))) -> False) x0.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ (((x0 x1) /\ (x1 = x2)) = (x1 = x2)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term268 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term276 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term321 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (y0 = x2))) y0.
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((fun y1 : a0 => y1 = x2) y0))) y0.
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (y1 = x2)) y0) y0.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> real, forall y2 : a0 -> real, (@FINITE a0 x0) -> (@sum a0 x0 (fun y3 : a0 => @COND real (y0 y3) (y1 y3) (y2 y3))) = (real_add (@sum a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 x0) /\ (y0 y4)) y4)) y1) (@sum a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 x0) /\ (~ (y0 y4))) y4)) y2)).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term301 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((fun y0 : a0 => y0 = x1) x2)).
Definition term168 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1))) x1.
Definition term297 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_neg (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))).
Definition term44 (x0 : Prop) := (~ x0) -> False.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0))) x2.
Definition term210 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_sub (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))).
Definition term163 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 x1 (fun y0 : a0 => @COND real (y0 = x2) x0 (x3 y0))) = (real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x2)) y1)) (fun y0 : a0 => x0)) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (y1 = x2))) y1)) x3)).
Definition term112 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 x1 (fun y0 : a0 => @COND real ((fun y1 : a0 => y1 = x2) y0) ((fun y1 : a0 => x0) y0) (x3 y0))) = (real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((fun y2 : a0 => y2 = x2) y1)) y1)) (fun y0 : a0 => x0)) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((fun y2 : a0 => y2 = x2) y1))) y1)) x3)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term256 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term324 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := (~ ((real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))) -> False.
Definition term111 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)) x0) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1)) x3).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((~ (x0 x1)) \/ (~ (x1 = x2))) /\ (x1 = x2).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term192 (a0 : Type') (x0 : real) (x1 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1)).
Definition term184 (a0 : Type') (x0 : a0) (x1 : real) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)) (fun y0 : a0 => x1).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (y0 = x2)) y0.
Definition term166 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0, ((@FINITE a0 y1) /\ (@IN a0 y2 y1)) -> (@sum a0 (@DELETE a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (y0 y2))) x0.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> real, forall y3 : a0 -> real, (@FINITE a0 y0) -> (@sum a0 y0 (fun y4 : a0 => @COND real (y1 y4) (y2 y4) (y3 y4))) = (real_add (@sum a0 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y0) /\ (y1 y5)) y5)) y2) (@sum a0 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y0) /\ (~ (y1 y5))) y5)) y3))) x0.
Definition term287 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x0)) (@sum a0 x1 x2)) (real_add (x2 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x1 x2))).
Definition term298 := real_neg (real_of_num (NUMERAL 0)).
Definition term292 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1)) (x0 x1)).
Definition term266 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term260 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1)).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => y2 = x1) y1))) y1)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1)).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => y2 = x1) y1)) y1)).
Definition term282 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term53 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (y0 x0) -> forall y1 : a0, ((y0 y1) /\ (y1 = x0)) = (y1 = x0).
Definition term326 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := ((@FINITE a0 x0) /\ (@IN a0 x3 x0)) -> (@sum a0 x0 (fun y0 : a0 => @COND real (y0 = x3) x1 (x2 y0))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1)) (fun y0 : a0 => x2).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => y2 = x1) y1)) y1)) (fun y0 : a0 => x2).
Definition term85 (x0 : Prop) := (~ x0) -> x0.
Definition term272 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1)) = (@INSERT a0 x1 (@EMPTY a0)).
Definition term222 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term118 (a0 : Type') (x0 : real) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((x0 x1) /\ (x1 = x2))) /\ (x1 = x2).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @sum a0 (@DELETE a0 x0 x1) x2.
Definition term264 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term191 (a0 : Type') (x0 : real) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0) := @COND real (x0 = x1).
Definition term302 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1)) = (@DELETE a0 x0 x1)).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (((x0 x1) /\ (x1 = x2)) /\ (~ (x1 = x2))) \/ ((~ ((x0 x1) /\ (x1 = x2))) /\ (x1 = x2)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (y2 = x1)) y1) y1.
Definition term226 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => y0 = (@DELETE a0 x0 x1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))).
Definition term267 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term259 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@IN a0 x0 x1).
Definition term244 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1))).
Definition term109 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 x1 (fun y0 : a0 => @COND real (x2 y0) (x0 y0) (x3 y0))) = (real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)) x0) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (x2 y1))) y1)) x3)).
Definition term186 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := real_add (@sum a0 (@INSERT a0 x3 (@EMPTY a0)) (fun y0 : a0 => x0)) (real_sub (@sum a0 x1 x2) (x2 x3)).
Definition term56 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, ((y1 y2) /\ (y2 = y0)) = (y2 = y0))) -> False.
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) (x3 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (x3 y0)).
Definition term248 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (x3 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x2 x3))).
Definition term142 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((fun y0 : a0 => y0 = x0) x1).
Definition term251 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3)) (real_add (x3 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x2 x3)))).
Definition term316 := real_lt (real_of_num (NUMERAL 0)).
Definition term194 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := real_add x0 (real_sub (@sum a0 x1 x2) (x2 x3)).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y2 = x1)) y2))) = (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, (@FINITE a0 x0) -> (@sum a0 x0 (fun y2 : a0 => @COND real (x1 y2) (y0 y2) (y1 y2))) = (real_add (@sum a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (x1 y3)) y3)) y0) (@sum a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ (x1 y3))) y3)) y1))) x2.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x2)) y1)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (y2 = x2)) y1) y1)).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term327 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := forall y0 : a0, ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 x0 (fun y1 : a0 => @COND real (y1 = y0) x1 (x2 y1))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 y0))).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, ((@FINITE a0 x0) /\ (@IN a0 y0 x0)) -> (@sum a0 (@DELETE a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (x1 y0)).
Definition term77 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term279 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term200 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_add (@sum a0 x0 x1).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (x1 = x2)).
Definition term275 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term235 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term228 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x2)) y1))).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (y2 = x2)) y1) y1))).
Definition term314 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term207 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := real_sub (real_add x0 (real_sub (@sum a0 x1 x2) (x2 x3))).
Definition term257 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := (real_gt (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))) (real_of_num (NUMERAL 0))).
Definition term323 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term299 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((fun y0 : a0 => y0 = x2) x3))) x3.
Definition term2 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0)) x1.
Definition term183 (a0 : Type') (x0 : a0) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, forall y2 : a0 -> real, (@FINITE a0 x0) -> (@sum a0 x0 (fun y3 : a0 => @COND real (y0 y3) (y1 y3) (y2 y3))) = (real_add (@sum a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 x0) /\ (y0 y4)) y4)) y1) (@sum a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 x0) /\ (~ (y0 y4))) y4)) y2))) x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False.
Definition term263 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x0 x1).
Definition term193 (a0 : Type') (x0 : real) (x1 : a0) := @eq real ((fun y0 : a0 => x0) x1).
Definition term290 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (x0 x1).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) (x3 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (x3 y0))).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) (x3 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => @COND real ((fun y1 : a0 => y1 = x1) y0) ((fun y1 : a0 => x2) y0) (x3 y0))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ (x1 = x2)) /\ (~ (x1 = x2)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y2 = x1)) y2))) = (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (y2 = y0))) y2)) = (@DELETE a0 x0 y0)) x1.
Definition term195 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @eq real (real_add x0 (real_sub (@sum a0 x1 x2) (x2 x3))).
Definition term188 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) (x3 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => @COND real ((fun y1 : a0 => y1 = x1) y0) ((fun y1 : a0 => x2) y0) (x3 y0)).
Definition term213 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_add (@sum a0 x0 x2) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x3))).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => y2 = x1) y1))) y1).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => y2 = x1) y1)) y1).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (y2 = x1)) y1) y1).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1).
Definition term107 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0 -> real, (@FINITE a0 x1) -> (@sum a0 x1 (fun y1 : a0 => @COND real (x2 y1) (x0 y1) (y0 y1))) = (real_add (@sum a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (x2 y2)) y2)) x0) (@sum a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ (x2 y2))) y2)) y0)).
Definition term309 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term318 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => y0 = x2) x3)).
Definition term189 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term285 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term269 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (y1 = x2)) y0) y0.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term199 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x1 x2)).
Definition term241 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term238 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ (y0 = x2))) y0.
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((fun y1 : a0 => y1 = x2) y0))) y0.
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => y1 = x2) y0)) y0.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (y0 = x2)) y0.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (((x0 x1) /\ (x1 = x2)) /\ (~ (x1 = x2))) \/ (((~ (x0 x1)) \/ (~ (x1 = x2))) /\ (x1 = x2)).
Definition term245 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (x0 x1).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x2 x0) /\ ((fun y0 : a0 => y0 = x1) x2).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term216 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x1 x2)).
Definition term291 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_of_num (NUMERAL 0)) (x0 x1).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x2 x1) /\ (~ (x2 = x3))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (y2 = y0))) y2)) = (@DELETE a0 x0 y0).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @sum a0 (@DELETE a0 x0 x1).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0) := @COND real ((fun y0 : a0 => y0 = x0) x1).
Definition term232 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1)) x2.
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := @sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => y2 = x1) y1))) y1)) x2.
Definition term320 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term246 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (x2 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x1 x2)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@DELETE a0 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (y2 = y0))) y2)).
Definition term265 := S (Nat.add 0 0).
Definition term224 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term254 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term57 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, ((y1 y2) /\ (y2 = y0)) = (y2 = y0).
Definition term164 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> real) := @eq real (real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x2)) y1)) (fun y0 : a0 => x0)) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (y1 = x2))) y1)) x3)).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1)) (fun y0 : a0 => x2)).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => y2 = x1) y1)) y1)) (fun y0 : a0 => x2)).
Definition term214 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term271 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, ((y0 y1) /\ (y1 = x0)) = (y1 = x0))) -> False) x1.
Definition term294 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x0 x1).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False.
Definition term54 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ ((y0 x0) -> forall y1 : a0, ((y0 y1) /\ (y1 = x0)) = (y1 = x0))) -> False.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1.
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((fun y2 : a0 => y2 = x1) y1))) y1.
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ ((fun y2 : a0 => y2 = x1) y1)) y1.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (y1 = x1)) y1.
Definition term277 := real_mul (real_of_num (NUMERAL 0)).
Definition term315 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term122 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0 -> real) (x3 : a0) := @COND real (x3 = x0) x1 (x2 x3).
Definition term114 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term161 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> real) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x2)) y1)) (fun y0 : a0 => x0)) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ (y1 = x2))) y1)) x3).
Definition term160 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> real) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ ((fun y2 : a0 => y2 = x2) y1)) y1)) (fun y0 : a0 => x0)) (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((fun y2 : a0 => y2 = x2) y1))) y1)) x3).
Definition term252 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term205 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x0)) (@sum a0 x1 x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((x0 x1) /\ (x1 = x2)).
Definition term219 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (x0 x1).
Definition term227 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> real, forall y1 : a0 -> real, (@FINITE a0 x0) -> (@sum a0 x0 (fun y2 : a0 => @COND real (x1 y2) (y0 y2) (y1 y2))) = (real_add (@sum a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (x1 y3)) y3)) y0) (@sum a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ (x1 y3))) y3)) y1)).
Definition term237 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term230 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term58 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, ((y1 y2) /\ (y2 = y0)) = (y2 = y0))) -> False.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or (((x0 x1) /\ (x1 = x2)) /\ (~ (x1 = x2))).
Definition term242 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term281 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term121 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0 -> real) (x3 : a0) := @COND real ((fun y0 : a0 => y0 = x0) x3) ((fun y0 : a0 => x1) x3) (x2 x3).
Definition term145 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((fun y0 : a0 => y0 = x2) x3))).
Definition term239 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term190 (a0 : Type') (x0 : real) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term123 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0 -> real) := fun y0 : a0 => @COND real ((fun y1 : a0 => y1 = x0) y0) ((fun y1 : a0 => x1) y0) (x2 y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (y0 = x1)) x2.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term148 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ (x3 = x2))) x3.
Definition term124 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0 -> real) := fun y0 : a0 => @COND real (y0 = x0) x1 (x2 y0).
Definition term270 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := ((~ ((real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))) -> False) -> (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))).
Definition term215 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x0)) (@sum a0 x1 x2)).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term236 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term212 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))).
Definition term119 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0) := @COND real ((fun y0 : a0 => y0 = x0) x2) ((fun y0 : a0 => x1) x2).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) \/ (@IN a0 x1 (@EMPTY a0)).
Definition term303 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term1 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0, (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x2 x1) /\ (x2 = x3)).
Definition term55 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (y0 x0) -> forall y1 : a0, ((y0 y1) /\ (y1 = x0)) = (y1 = x0).
Definition term84 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term233 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term249 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))).
Definition term240 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term280 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term229 := real_of_num (NUMERAL (BIT1 0)).
Definition term247 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_mul (real_of_num (NUMERAL 0)) (@sum a0 x0 x1).
Definition term187 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @eq real (real_add (@sum a0 (@INSERT a0 x3 (@EMPTY a0)) (fun y0 : a0 => x0)) (real_sub (@sum a0 x1 x2) (x2 x3))).
Definition term182 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @eq real (real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x3)) y1)) (fun y0 : a0 => x0)) (real_sub (@sum a0 x1 x2) (x2 x3))).
Definition term284 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term185 (a0 : Type') (x0 : a0) (x1 : real) := real_add (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) (fun y0 : a0 => x1)).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_add (@sum a0 x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x0 x1)).
Definition term74 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ ((fun y1 : a0 => y1 = x2) y0)) y0.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term308 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_gt (real_neg (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))) (real_of_num (NUMERAL 0)).
Definition term311 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_gt (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))) (real_of_num (NUMERAL 0)).
Definition term98 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (y3 = y1))) y3)) = (@DELETE a0 y0 y1).
Definition term319 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term97 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (@DELETE a0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (y3 = y1))) y3)).
Definition term218 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1)).
Definition term313 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ((@FINITE a0 x0) /\ (@IN a0 x2 x0)) -> (@sum a0 (@DELETE a0 x0 x2) x1) = (real_sub (@sum a0 x0 x1) (x1 x2)).
Definition term288 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x0)) (x2 x0)) (real_add (@sum a0 x1 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x1 x2))).
Definition term231 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term306 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := real_gt (real_neg (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (((x0 x1) /\ (x1 = x2)) = (x1 = x2))) -> False.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@DELETE a0 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (y2 = y0))) y2)).
Definition term296 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> ((~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (y0 = x2)) x3) x3.
Definition term52 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, ((y0 y1) /\ (y1 = x0)) = (y1 = x0))) -> False.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (x1 = x2).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := and (~ ((x0 x1) /\ (x1 = x2))).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((x0 x1) -> forall y0 : a0, ((x0 y0) /\ (y0 = x1)) = (y0 = x1))) -> False.
Definition term289 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1)) (x0 x1).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (y2 = y0))) y2)) = (@DELETE a0 x0 y0).
Definition term243 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_of_num (NUMERAL (BIT1 0))) (x0 x1).
Definition term113 (a0 : Type') (x0 : real) := fun y0 : a0 => x0.
Definition term317 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term258 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term255 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((x0 y0) /\ (y0 = x1)) = (y0 = x1).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => y0 = x0) x1.
Definition term108 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> real) := (fun y0 : a0 -> real => (@FINITE a0 x1) -> (@sum a0 x1 (fun y1 : a0 => @COND real (x2 y1) (x0 y1) (y0 y1))) = (real_add (@sum a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (x2 y2)) y2)) x0) (@sum a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ (x2 y2))) y2)) y0))) x3.
Definition term225 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term304 := real_div (real_of_num (NUMERAL 0)).
Definition term286 := real_add (real_of_num (NUMERAL 0)).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := @eq real (real_neg (real_sub (real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3))))).
Definition term59 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, ((y1 y2) /\ (y2 = y0)) = (y2 = y0).
Definition term198 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0) := real_sub x0 (x1 x2).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term86 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 x0) /\ (y0 = x1).
Definition term202 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := real_add x0 (real_add (@sum a0 x1 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x2 x3))).
Definition term328 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 y0 (fun y2 : a0 => @COND real (y2 = y1) x0 (x1 y2))) = (real_add (@sum a0 y0 x1) (real_sub x0 (x1 y1))).
Definition term167 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0, ((@FINITE a0 y0) /\ (@IN a0 y1 y0)) -> (@sum a0 (@DELETE a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (x0 y1)).
Definition term100 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (y3 = y1))) y3)) = (@DELETE a0 y0 y1).
Definition term99 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@DELETE a0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (y3 = y1))) y3)).
Definition term278 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term211 (a0 : Type') (x0 : real) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> real) := real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x3 x1)) (@sum a0 x2 x3)))).
Definition term223 := NUMERAL (BIT1 0).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ ((fun y0 : a0 => y0 = x2) x3)) x3.
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : real) := @COND real (x0 = x1) x2.
Definition term253 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 -> Prop => y0 = (@DELETE a0 x0 x1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (y1 = x1))) y1))).
Definition term76 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) (x3 : a0) := ~ ((real_add x1 (real_sub (@sum a0 x0 x2) (x2 x3))) = (real_add (@sum a0 x0 x2) (real_sub x1 (x2 x3)))).
Definition term181 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := real_add (@sum a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (y1 = x3)) y1)) (fun y0 : a0 => x0)) (real_sub (@sum a0 x1 x2) (x2 x3)).
Definition term322 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term203 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1).
Definition term307 := real_gt (real_of_num (NUMERAL 0)).
