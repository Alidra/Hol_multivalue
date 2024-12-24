Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term297 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop (((forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2)).
Definition term45 (x0 : real) (x1 : real) := ~ ((forall y0 : real, (@IN real y0 (@EMPTY real)) -> real_le x0 y0) = (real_le x0 x1)).
Definition term125 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term140 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term263 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le y0 (x1 y0))).
Definition term76 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term230 (x0 : real -> Prop) := ~ (all x0).
Definition term184 := (~ False) -> False.
Definition term59 (x0 : real) := fun y0 : real => ~ (real_le y0 x0).
Definition term87 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term22 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1).
Definition term145 (x0 : real) := (~ (~ (real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0))) -> False.
Definition term38 (x0 : real) (x1 : real) := (fun y0 : real => (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)) x1.
Definition term17 (x0 : real -> Prop) := forall y0 : real, (has_inf x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) = (real_le y1 y0)).
Definition term286 (x0 : real -> real) (x1 : real) := (~ (real_le x1 (x0 x1))) -> real_le x1 (x0 x1).
Definition term108 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term273 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (@IN real (x0 x1) x2)) -> @IN real (x0 x1) x2.
Definition term115 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term116 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term75 (x0 : nat) := real_neg (real_of_num x0).
Definition term271 (x0 : real -> real) (x1 : real) := ~ (real_le x1 (x0 x1)).
Definition term61 (x0 : Prop) := ~ (~ x0).
Definition term107 := real_of_num (NUMERAL 0).
Definition term236 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term48 (x0 : real) := exists y0 : real, ~ ((forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)).
Definition term327 (x0 : real -> Prop) (x1 : real) := ((forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)) -> (~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1))) /\ (((~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1))) -> forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)).
Definition term114 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term118 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term68 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term160 := (forall y0 : real, real_le y0 y0) -> False.
Definition term261 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) /\ (~ (real_le x2 (x1 x2))).
Definition term136 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term322 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((forall y0 : real, (@IN real y0 x1) -> real_le x2 y0) -> real_le x2 x0) /\ ((real_le x2 x0) -> forall y0 : real, (@IN real y0 x1) -> real_le x2 y0).
Definition term24 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term81 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term195 (x0 : real -> Prop) := True /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term153 (x0 : Prop) := (~ x0) -> False.
Definition term53 := fun y0 : real => True.
Definition term316 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term311 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term199 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False.
Definition term231 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term32 (x0 : real) := ~ (forall y0 : real, (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)).
Definition term225 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x2 x0)) \/ (real_le x1 x2).
Definition term98 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term102 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term312 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term27 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) = (real_le y1 x0)) x1.
Definition term323 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) /\ (((forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2)).
Definition term141 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term161 := ~ (forall y0 : real, real_le y0 y0).
Definition term324 (x0 : real -> Prop) (x1 : real) (x2 : real) := (((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2).
Definition term176 (x0 : real) := forall y0 : real, ~ (real_le y0 x0).
Definition term200 (x0 : real) (x1 : real) (x2 : real -> Prop) := (((~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False.
Definition term112 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term106 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term44 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)) x1).
Definition term35 (x0 : real) := ~ (forall y0 : real, (fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0).
Definition term279 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term124 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term49 (x0 : real) := imp (@IN real x0 (@EMPTY real)).
Definition term293 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => ((forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> real_le y1 y0)) -> (forall y1 : real, (@IN real y1 x0) -> real_le x1 y1) = (real_le x1 x2)) x2.
Definition term256 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y2 y3))) y0 y1.
Definition term165 := fun y0 : real => (~ (exists y1 : real, real_le y1 y0)) -> (forall y1 : real, real_le y1 y1) -> False.
Definition term212 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (~ (x1 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> ((inf x1) = x0) -> exists y1 : real, forall y2 : real, (@IN real y2 x1) -> real_le y1 y2.
Definition term222 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, (~ (y0 = (@EMPTY real))) -> (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> ((inf y0) = y1) -> exists y3 : real, forall y4 : real, (@IN real y4 y0) -> real_le y3 y4.
Definition term221 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, (~ (y0 = (@EMPTY real))) -> (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> ((inf y0) = y1) -> (~ (exists y3 : real, forall y4 : real, (@IN real y4 y0) -> real_le y3 y4)) -> False.
Definition term9 := (forall y0 : real -> Prop, forall y1 : real, (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1)) -> (inf y0) = y1) -> forall y0 : real -> Prop, forall y1 : real, (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1)) -> (inf y0) = y1.
Definition term54 := forall y0 : real, True.
Definition term209 (x0 : real -> Prop) := imp (~ (x0 = (@EMPTY real))).
Definition term220 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, (~ (y0 = (@EMPTY real))) -> (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> ((inf y0) = y1) -> exists y3 : real, forall y4 : real, (@IN real y4 y0) -> real_le y3 y4.
Definition term219 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, (~ (y0 = (@EMPTY real))) -> (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> ((inf y0) = y1) -> (~ (exists y3 : real, forall y4 : real, (@IN real y4 y0) -> real_le y3 y4)) -> False.
Definition term52 (x0 : real) := fun y0 : real => (@IN real y0 (@EMPTY real)) -> real_le x0 y0.
Definition term214 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (~ (x1 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> ((inf x1) = x0) -> exists y1 : real, forall y2 : real, (@IN real y2 x1) -> real_le y1 y2.
Definition term213 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (~ (x1 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> ((inf x1) = x0) -> (~ (exists y1 : real, forall y2 : real, (@IN real y2 x1) -> real_le y1 y2)) -> False.
Definition term203 (x0 : real -> Prop) (x1 : real) := imp ((inf x0) = x1).
Definition term56 (x0 : Prop) := forall y0 : real, x0.
Definition term181 (x0 : Prop) := (~ x0) -> x0.
Definition term7 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1).
Definition term91 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term233 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2.
Definition term278 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x0 x1) \/ (~ (@IN real x1 x2))).
Definition term77 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) -> (forall y1 : real, (@IN real y1 y0) -> real_le (inf y0) y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) -> real_le y1 (inf y0))) x0.
Definition term133 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term244 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term50 (x0 : real) (x1 : real) := (@IN real x1 (@EMPTY real)) -> real_le x0 x1.
Definition term110 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term270 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le y0 (x1 y0)))) x2.
Definition term196 (x0 : real -> Prop) := (~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> False.
Definition term154 (x0 : real) := (~ (exists y0 : real, real_le y0 x0)) -> False.
Definition term315 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term304 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term302 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term218 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, (~ (x0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> ((inf x0) = y0) -> exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3.
Definition term217 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, (~ (x0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> ((inf x0) = y0) -> (~ (exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3)) -> False.
Definition term162 := forall y0 : real, real_le y0 y0.
Definition term135 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term229 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) /\ (~ (real_le x1 x2)).
Definition term268 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le y1 (y0 y1))).
Definition term249 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y2 y3))) y1 (y0 y1).
Definition term247 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term67 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term97 (x0 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term171 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term18 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (has_inf x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) = (real_le y1 y0))) x1.
Definition term139 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : real) := real_add x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term113 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term262 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y1 y2))) y0 (x1 y0).
Definition term308 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term163 (x0 : real) := imp (~ (exists y0 : real, real_le y0 x0)).
Definition term198 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False.
Definition term134 := real_le (real_of_num (NUMERAL 0)).
Definition term142 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term180 (x0 : real) := ~ (real_le x0 x0).
Definition term6 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)) -> (inf x0) = x1.
Definition term232 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term36 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0).
Definition term69 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term299 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 x1.
Definition term16 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (has_inf y0 y1) = (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1))) x0.
Definition term3 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1)) -> (inf y0) = y1) x0.
Definition term197 (x0 : real -> Prop) := ~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term259 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y0 y1))) x2 (x1 x2).
Definition term272 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := @IN real (x0 x1) x2.
Definition term320 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> (real_le x1 x2) = True.
Definition term284 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) -> real_le x2 (x1 x2).
Definition term66 (x0 : real) := real_sub x0 (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term241 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) y0).
Definition term186 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term57 (x0 : real) := @eq Prop (forall y0 : real, (@IN real y0 (@EMPTY real)) -> real_le x0 y0).
Definition term20 (x0 : real -> Prop) (x1 : real) := @eq Prop (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)).
Definition term21 (x0 : real -> Prop) (x1 : real) := (~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term144 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term242 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y0 y1)).
Definition term274 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ~ (@IN real (x0 x1) x2).
Definition term300 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 x1) x2.
Definition term275 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x0 x1) \/ (~ (@IN real x1 x2)).
Definition term216 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (~ (x0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> ((inf x0) = y0) -> exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3.
Definition term215 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (~ (x0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> ((inf x0) = y0) -> (~ (exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3)) -> False.
Definition term47 (x0 : real) := fun y0 : real => ~ ((forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)).
Definition term179 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term121 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term117 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term88 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term280 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x2 x0))) -> real_le x1 x2.
Definition term103 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term201 (x0 : real) (x1 : real) (x2 : real -> Prop) := (((~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> ((~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False) -> (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False.
Definition term310 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term60 (x0 : real) := exists y0 : real, ~ (real_le y0 x0).
Definition term314 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term151 (x0 : real) := fun y0 : real => real_le y0 x0.
Definition term276 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term143 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term92 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term296 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2).
Definition term294 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((forall y0 : real, (@IN real y0 x0) -> real_le x2 y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 x2)) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2).
Definition term4 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) = (real_le y1 y0)) -> (inf x0) = y0.
Definition term175 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => real_le y1 x0) y0).
Definition term313 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term158 (x0 : real) := (((~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term109 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term258 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y0 y1))).
Definition term257 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y2 y3))) y0 y1).
Definition term269 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0)) x2.
Definition term188 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1).
Definition term30 (x0 : real) (x1 : real -> Prop) := @eq Prop ((fun y0 : real -> Prop => forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) = (real_le y1 x0)) x1).
Definition term210 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (x2 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term298 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 x1).
Definition term192 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term194 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term147 (x0 : real) := ~ (real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term127 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term130 (x0 : real) := real_ge (real_sub x0 (real_add x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term89 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term252 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y0 y1))) x1 x2.
Definition term285 (x0 : real -> real) (x1 : real) := real_le x1 (x0 x1).
Definition term170 (x0 : real -> Prop) := ~ (ex x0).
Definition term187 (x0 : real) (x1 : real) := @eq Prop (real_le x0 x1).
Definition term248 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y2 y3))) y0 y1.
Definition term246 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term243 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y0 y1)).
Definition term224 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le x1 y0.
Definition term23 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term150 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term51 (x0 : real) (x1 : real) := False -> real_le x0 x1.
Definition term93 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : real) := real_ge (real_sub x0 (real_add x0 (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term260 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x2 y0))) (x1 x2).
Definition term34 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term208 (x0 : real) (x1 : real) (x2 : real -> Prop) := (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1.
Definition term31 (x0 : real) := (forall y0 : real, (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0)) -> False.
Definition term234 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2).
Definition term317 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term301 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) -> real_le x1 x2.
Definition term85 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term321 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x2 x0) -> forall y0 : real, (@IN real y0 x1) -> real_le x2 y0.
Definition term131 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term283 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term326 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)) -> (~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1)).
Definition term138 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term111 := S (Nat.add 0 0).
Definition term78 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term25 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term281 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term101 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term169 := fun y0 : real => real_le y0 y0.
Definition term325 (x0 : real -> Prop) (x1 : real) := ((~ (x0 = (@EMPTY real))) /\ ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ ((inf x0) = x1))) -> forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1).
Definition term70 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term41 (x0 : real) := forall y0 : real, (fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0.
Definition term39 (x0 : real) := forall y0 : real, (@IN real y0 (@EMPTY real)) -> real_le x0 y0.
Definition term80 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 := real_mul (real_of_num (NUMERAL 0)).
Definition term305 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term289 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (~ (x0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> ((inf x0) = y0) -> (~ (exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3)) -> False) x1.
Definition term239 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) x1.
Definition term99 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term174 (x0 : real) (x1 : real) := ~ ((fun y0 : real => real_le y0 x0) x1).
Definition term265 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le y0 (x1 y0))).
Definition term28 (x0 : real) := (fun y0 : real -> Prop => forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) = (real_le y1 x0)) (@EMPTY real).
Definition term254 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y1 y2))) x1 y0.
Definition term148 (x0 : real -> Prop) := (x0 = (@EMPTY real)) -> False.
Definition term226 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term83 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term62 (x0 : real) := ~ (~ (real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term264 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y1 y2))) y0 (x1 y0).
Definition term123 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term307 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term149 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) = (real_le y0 x1)) x2.
Definition term73 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term329 := forall y0 : real -> Prop, forall y1 : real, (has_inf y0 y1) = ((~ (y0 = (@EMPTY real))) /\ ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ ((inf y0) = y1))).
Definition term2 := forall y0 : real -> Prop, forall y1 : real, (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1)) -> (inf y0) = y1.
Definition term146 (x0 : real) := ((~ (~ (real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0))) -> False) -> ~ (real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term189 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ (x1 -> x2)) -> (x0 -> x1) -> x2.
Definition term40 (x0 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0.
Definition term90 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term167 := forall y0 : real, (~ (exists y1 : real, real_le y1 y0)) -> (forall y1 : real, real_le y1 y1) -> False.
Definition term211 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (~ (x1 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> ((inf x1) = x0) -> (~ (exists y1 : real, forall y2 : real, (@IN real y2 x1) -> real_le y1 y2)) -> False.
Definition term204 (x0 : real) (x1 : real -> Prop) := ((inf x1) = x0) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) -> False.
Definition term43 (x0 : real) := @eq Prop (~ (forall y0 : real, (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0))).
Definition term42 (x0 : real) := @eq Prop (~ (forall y0 : real, (fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0)).
Definition term240 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) x1).
Definition term318 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term178 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term267 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le y1 (y0 y1))).
Definition term266 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y2 y3))) y1 (y0 y1).
Definition term26 (x0 : real) := fun y0 : real -> Prop => forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) = (real_le y1 x0).
Definition term33 (x0 : real -> Prop) := ~ (forall y0 : real, x0 y0).
Definition term288 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, (~ (y0 = (@EMPTY real))) -> (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> ((inf y0) = y1) -> (~ (exists y3 : real, forall y4 : real, (@IN real y4 y0) -> real_le y3 y4)) -> False) x0.
Definition term155 (x0 : real) := ~ (exists y0 : real, real_le y0 x0).
Definition term58 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term237 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term86 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term227 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term94 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term292 (x0 : real) (x1 : real) (x2 : real -> Prop) := (fun y0 : real => ((forall y1 : real, (@IN real y1 x2) -> real_le y0 y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x2) -> real_le y1 y2) -> real_le y1 y0)) -> (forall y1 : real, (@IN real y1 x2) -> real_le x0 y1) = (real_le x0 x1)) (inf x2).
Definition term122 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term71 := real_of_num (NUMERAL (BIT1 0)).
Definition term306 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term95 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term152 (x0 : real) := exists y0 : real, real_le y0 x0.
Definition term129 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term126 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term250 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y0 y1)).
Definition term319 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term29 (x0 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0).
Definition term63 (x0 : real) := real_le (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term19 (x0 : real -> Prop) (x1 : real) := @eq Prop (has_inf x0 x1).
Definition term309 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term5 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) = (real_le y1 y0)) -> (inf x0) = y0) x1.
Definition term253 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x1 y0))) x2.
Definition term185 (x0 : real) := (fun y0 : real => (~ (exists y1 : real, real_le y1 y0)) -> (forall y1 : real, real_le y1 y1) -> False) x0.
Definition term238 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) y0).
Definition term172 (x0 : real) := forall y0 : real, ~ ((fun y1 : real => real_le y1 x0) y0).
Definition term206 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term156 (x0 : real) := (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term235 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term46 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (forall y2 : real, (@IN real y2 (@EMPTY real)) -> real_le y1 y2) = (real_le y1 x0)) y0).
Definition term137 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term190 (x0 : real -> Prop) (x1 : real) (x2 : real) := (((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) /\ (((forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2))) -> (((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0))) -> (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0) = (real_le x1 x2).
Definition term168 := forall y0 : real, (~ (exists y1 : real, real_le y1 y0)) -> ~ (forall y1 : real, real_le y1 y1).
Definition term193 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) -> (x0 = (@EMPTY real)) = False.
Definition term15 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term295 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((fun y0 : real => ((forall y1 : real, (@IN real y1 x2) -> real_le y0 y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x2) -> real_le y1 y2) -> real_le y1 y0)) -> (forall y1 : real, (@IN real y1 x2) -> real_le x0 y1) = (real_le x0 x1)) (inf x2)).
Definition term223 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> real_le x1 x2.
Definition term84 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term166 := fun y0 : real => (~ (exists y1 : real, real_le y1 y0)) -> ~ (forall y1 : real, real_le y1 y1).
Definition term207 (x0 : real) (x1 : real) (x2 : real -> Prop) := (forall y0 : real, (@IN real y0 x2) -> real_le x0 y0) -> ((inf x2) = x1) -> (~ (exists y0 : real, forall y1 : real, (@IN real y1 x2) -> real_le y0 y1)) -> False.
Definition term277 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x2 x0)) \/ (real_le x1 x2)).
Definition term251 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y0 y1))) x1.
Definition term205 (x0 : real) (x1 : real -> Prop) := ((inf x1) = x0) -> exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1.
Definition term177 (x0 : real) (x1 : real) := (fun y0 : real => ~ (real_le y0 x0)) x1.
Definition term157 (x0 : real) := ((~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term96 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term287 (x0 : real -> real) (x1 : real) := (real_le x1 (x0 x1)) -> False.
Definition term255 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y1 y2))) x1 y0.
Definition term290 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (~ (x1 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) -> ((inf x1) = x0) -> (~ (exists y1 : real, forall y2 : real, (@IN real y2 x1) -> real_le y1 y2)) -> False) x2.
Definition term159 (x0 : real) := (((~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> ((~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False) -> (~ (exists y0 : real, real_le y0 x0)) -> (forall y0 : real, real_le y0 y0) -> False.
Definition term104 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term72 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term202 (x0 : real -> Prop) := ~ (~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term132 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term79 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term173 (x0 : real) (x1 : real) := (fun y0 : real => real_le y0 x0) x1.
Definition term245 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term183 (x0 : real) := (real_le x0 x0) -> False.
Definition term228 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x2 x0) -> real_le x1 x2).
Definition term182 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term128 := real_add (real_of_num (NUMERAL 0)).
Definition term291 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> real_le y1 y0)) -> (forall y1 : real, (@IN real y1 x0) -> real_le x1 y1) = (real_le x1 x2).
Definition term303 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term164 (x0 : real) := (~ (exists y0 : real, real_le y0 x0)) -> ~ (forall y0 : real, real_le y0 y0).
Definition term120 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real -> Prop) (x1 : real) := (forall y0 : real -> Prop, forall y1 : real, (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) = (real_le y2 y1)) -> (inf y0) = y1) -> (inf x0) = x1.
Definition term328 (x0 : real -> Prop) := forall y0 : real, (has_inf x0 y0) = ((~ (x0 = (@EMPTY real))) /\ ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ ((inf x0) = y0))).
Definition term1 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) -> (forall y0 : real, (@IN real y0 x0) -> real_le (inf x0) y0) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) -> real_le y0 (inf x0)).
Definition term74 := NUMERAL (BIT1 0).
Definition term100 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term37 (x0 : real) := fun y0 : real => (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1) = (real_le y0 x0).
Definition term82 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term13 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term191 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term282 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
