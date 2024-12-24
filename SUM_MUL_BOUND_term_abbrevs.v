Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (a0 : Type') (x0 : real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (real_mul x0 (@sum a0 y0 x1)) = (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (real_le (x1 x3) (@sum a0 x0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 x3)).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) = x4) -> (x4 -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = x5) -> ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3)) = (x4 -> x5).
Definition term13 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => (x0 y0) = (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@SUBSET a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (@IN a0 y1 y0)) x0.
Definition term20 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0, (y0 y1) = (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0)) x0.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@DIFF a0 x0 x1)) = ((@IN a0 y0 x0) /\ (~ (@IN a0 y0 x1))).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0)).
Definition term151 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term66 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (real_mul x0 (@sum a0 y0 x1)) = (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1)))) x2.
Definition term29 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> real_le (real_mul (x1 x3) (x2 x3)) (real_mul (@sum a0 x0 x1) (x2 x3)).
Definition term157 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> (real_le (real_of_num (NUMERAL 0)) (y0 y3)) /\ (real_le (real_of_num (NUMERAL 0)) (y1 y3)))) -> real_le (@sum a0 y2 (fun y3 : a0 => real_mul (y0 y3) (y1 y3))) (real_mul (@sum a0 y2 y0) (@sum a0 y2 y1)).
Definition term63 (a0 : Type') := forall y0 : a0 -> real, forall y1 : real, forall y2 : a0 -> Prop, (real_mul y1 (@sum a0 y2 y0)) = (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))).
Definition term62 (a0 : Type') := forall y0 : a0 -> real, forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0)).
Definition term45 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2).
Definition term33 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (forall y3 : a0, (@IN a0 y3 (@DIFF a0 y1 y0)) -> real_le (real_of_num (NUMERAL 0)) (y2 y3)))) -> real_le (@sum a0 y0 y2) (@sum a0 y1 y2).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@DIFF a0 x0 y0)) = ((@IN a0 y1 x0) /\ (~ (@IN a0 y1 y0)))) x1.
Definition term32 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := True /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_mul (x1 y0) (x2 y0)) (real_mul (@sum a0 x0 x1) (x2 y0))).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := ((real_le (x1 x3) (@sum a0 x0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 x3))) -> real_le (real_mul (x1 x3) (x2 x3)) (real_mul (@sum a0 x0 x1) (x2 x3)).
Definition term75 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 => real_mul (x0 y0) (x1 y0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_mul (x1 y0) (x2 y0)) (real_mul (@sum a0 x0 x1) (x2 y0)).
Definition term150 (a0 : Type') := forall y0 : a0, True.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := real_le ((fun y0 : a0 => real_mul (x1 y0) (x2 y0)) x3) ((fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0)) x3).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@DIFF a0 y0 y1)) = ((@IN a0 y2 y0) /\ (~ (@IN a0 y2 y1)))) x0.
Definition term64 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (real_mul y1 (@sum a0 y2 y0)) = (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3)))) x0.
Definition term47 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2)) x0.
Definition term34 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (forall y3 : a0, (@IN a0 y3 (@DIFF a0 y1 y0)) -> real_le (real_of_num (NUMERAL 0)) (y2 y3)))) -> real_le (@sum a0 y0 y2) (@sum a0 y1 y2)) x0.
Definition term49 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : a0 -> real => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) (y0 y1))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 y0)) x2.
Definition term38 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1)) x2.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : a0 -> real => ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (forall y1 : a0, (@IN a0 y1 (@DIFF a0 x1 x0)) -> real_le (real_of_num (NUMERAL 0)) (y0 y1)))) -> real_le (@sum a0 x0 y0) (@sum a0 x1 y0)) x2.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_mul (x1 y0) (x2 y0)) (real_mul (@sum a0 x0 x1) (x2 y0)).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 y0)).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0).
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DIFF a0 x1 (@INSERT a0 x2 (@EMPTY a0))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul x1 (x2 y0)).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)) -> real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term109 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term46 (a0 : Type') := (forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> real_le (y0 y3) (y2 y3))) -> real_le (@sum a0 y1 y0) (@sum a0 y1 y2).
Definition term10 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (forall y3 : a0, (@IN a0 y3 (@DIFF a0 y1 y0)) -> real_le (real_of_num (NUMERAL 0)) (y2 y3)))) -> real_le (@sum a0 y0 y2) (@sum a0 y1 y2)) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (forall y3 : a0, (@IN a0 y3 (@DIFF a0 y1 y0)) -> real_le (real_of_num (NUMERAL 0)) (y2 y3)))) -> real_le (@sum a0 y0 y2) (@sum a0 y1 y2).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> (real_le (real_of_num (NUMERAL 0)) (x1 x3)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 x3)).
Definition term82 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := real_mul (x0 x2) (x1 x2).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0).
Definition term61 (a0 : Type') := fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (real_mul y1 (@sum a0 y2 y0)) = (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))).
Definition term60 (a0 : Type') := fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0)).
Definition term28 (x0 : real) (x1 : real) (x2 : real) := ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2)) -> real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) x2) (@sum a0 x1 x2).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 (@DIFF a0 x0 x1)) = ((@IN a0 y0 x0) /\ (~ (@IN a0 y0 x1)))) x2.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := @eq real ((fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0)) x3).
Definition term155 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> (real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) -> real_le (@sum a0 y0 (fun y1 : a0 => real_mul (x0 y1) (x1 y1))) (real_mul (@sum a0 y0 x0) (@sum a0 y0 x1)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := real_le (@sum a0 x0 (fun y0 : a0 => real_mul (x1 y0) (x2 y0))) (@sum a0 x0 (fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0))).
Definition term59 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (real_mul y0 (@sum a0 y1 x0)) = (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))).
Definition term58 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term24 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1).
Definition term22 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((@IN a0 x1 x0) /\ (~ (@IN a0 x1 (@INSERT a0 x2 (@EMPTY a0))))) -> True.
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0)) x1.
Definition term48 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> real_le (x0 y2) (y1 y2))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 y1)) x1.
Definition term36 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (forall y2 : a0, (@IN a0 y2 (@DIFF a0 y0 x0)) -> real_le (real_of_num (NUMERAL 0)) (y1 y2)))) -> real_le (@sum a0 x0 y1) (@sum a0 y0 y1)) x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (@FINITE a0 x0) /\ ((@SUBSET a0 x1 x0) /\ (forall y0 : a0, (@IN a0 y0 (@DIFF a0 x0 x1)) -> real_le (real_of_num (NUMERAL 0)) (x2 y0))).
Definition term26 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> (real_le (real_of_num (NUMERAL 0)) (x1 x2)) = True.
Definition term16 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term15 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0, (x0 y0) = (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term141 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) (x4 : Prop) := ((@IN a0 x2 (@DIFF a0 x1 (@INSERT a0 x3 (@EMPTY a0)))) = ((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0)))))) -> (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> (real_le (real_of_num (NUMERAL 0)) (x0 x2)) = x4) -> ((@IN a0 x2 (@DIFF a0 x1 (@INSERT a0 x3 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x0 x2)) = (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> x4).
Definition term131 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> real_le ((fun y0 : a0 => real_mul (x1 y0) (x2 y0)) x3) ((fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0)) x3).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 (@INSERT a0 x2 (@EMPTY a0)))).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term51 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul x0 (@sum a0 x1 x2).
Definition term72 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 (fun y0 : a0 => real_mul (x0 y0) (x2 y0))) (real_mul (@sum a0 x1 x0) (@sum a0 x1 x2)).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0).
Definition term78 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := (@FINITE a0 x0) /\ ((@SUBSET a0 (@INSERT a0 x1 (@EMPTY a0)) x0) /\ (forall y0 : a0, (@IN a0 y0 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 y0))).
Definition term144 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> (real_le (real_of_num (NUMERAL 0)) (x0 x2)) = True) -> ((@IN a0 x2 (@DIFF a0 x1 (@INSERT a0 x3 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x0 x2)) = (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> True).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 y0))) x3.
Definition term148 (a0 : Type') := fun y0 : a0 => True.
Definition term79 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := real_le (real_mul (x1 x3) (x2 x3)) (real_mul (@sum a0 x0 x1) (x2 x3)).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := real_le (@sum a0 x0 (fun y0 : a0 => real_mul (x1 y0) (x2 y0))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0))) -> real_le (@sum a0 x0 (fun y0 : a0 => real_mul (x1 y0) (x2 y0))) (@sum a0 x0 (fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0))).
Definition term42 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term83 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => real_mul (x0 y1) (x1 y1)) y0.
Definition term41 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term21 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => (x0 y0) = (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0)) x1.
Definition term80 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_mul (x0 y1) (x1 y1)) y0) x2.
Definition term87 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := real_le (real_mul (x0 x2) (x1 x2)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => real_mul (@sum a0 x0 x1) (x2 y0)) x3.
Definition term56 (a0 : Type') (x0 : a0 -> real) := fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term81 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => real_mul (x0 y0) (x1 y0)) x2.
Definition term142 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) (x4 : Prop) := (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> (real_le (real_of_num (NUMERAL 0)) (x0 x2)) = x4) -> ((@IN a0 x2 (@DIFF a0 x1 (@INSERT a0 x3 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x0 x2)) = (((@IN a0 x2 x1) /\ (~ (@IN a0 x2 (@INSERT a0 x3 (@EMPTY a0))))) -> x4).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := forall y0 : Prop, ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) = x4) -> (x4 -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = y0) -> ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3)) = (x4 -> y0).
Definition term132 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term17 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0, (y0 y1) = (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 y0).
Definition term65 (a0 : Type') (x0 : a0 -> real) (x1 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (real_mul y0 (@sum a0 y1 x0)) = (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2)))) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> real, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (forall y3 : a0, (@IN a0 y3 (@DIFF a0 y1 y0)) -> real_le (real_of_num (NUMERAL 0)) (y2 y3)))) -> real_le (@sum a0 y0 y2) (@sum a0 y1 y2)) -> real_le (@sum a0 x0 x2) (@sum a0 x1 x2).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) = y0) -> (y0 -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = y1) -> ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3)) = (y0 -> y1).
Definition term133 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term25 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1)) x1.
Definition term86 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := real_le ((fun y0 : a0 => real_mul (x0 y0) (x1 y0)) x2).
Definition term27 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0)) x2.
Definition term30 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term156 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> (real_le (real_of_num (NUMERAL 0)) (x0 y2)) /\ (real_le (real_of_num (NUMERAL 0)) (y0 y2)))) -> real_le (@sum a0 y1 (fun y2 : a0 => real_mul (x0 y2) (y0 y2))) (real_mul (@sum a0 y1 x0) (@sum a0 y1 y0)).
Definition term44 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> real_le (x0 y2) (y1 y2))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 y1).
Definition term35 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (forall y2 : a0, (@IN a0 y2 (@DIFF a0 y0 x0)) -> real_le (real_of_num (NUMERAL 0)) (y1 y2)))) -> real_le (@sum a0 x0 y1) (@sum a0 y0 y1).
Definition term12 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term108 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := (real_le (real_of_num (NUMERAL 0)) (x0 x2)) /\ (real_le (real_of_num (NUMERAL 0)) (x1 x2)).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := (@SUBSET a0 (@INSERT a0 x1 (@EMPTY a0)) x0) /\ (forall y0 : a0, (@IN a0 y0 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 y0)).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) = x4) -> (x4 -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = y0) -> ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3)) = (x4 -> y0)) x5.
Definition term55 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (real_mul x0 (@sum a0 y0 x1)) = (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x0 x2) (@sum a0 x1 x2).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := real_mul (@sum a0 x0 x1) (x2 x3).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3).
Definition term14 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0, (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term85 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := @eq real ((fun y0 : a0 => real_mul (x0 y0) (x1 y0)) x2).
Definition term39 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ ((@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1) /\ (forall y0 : a0, (@IN a0 y0 (@DIFF a0 x1 (@INSERT a0 x0 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 y0)))) -> real_le (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) x2) (@sum a0 x1 x2).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (x2 x0) (@sum a0 x1 x2).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (forall y0 : a0, (@IN a0 y0 (@DIFF a0 x1 x0)) -> real_le (real_of_num (NUMERAL 0)) (x2 y0)))) -> real_le (@sum a0 x0 x2) (@sum a0 x1 x2).
Definition term113 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (real_le (x2 x0) (@sum a0 x1 x2)) /\ True.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le ((fun y1 : a0 => real_mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 y0))).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) (x2 y0)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0) x3).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term52 (a0 : Type') (x0 : real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 y0).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_mul (@sum a0 x0 x1) (x2 y1)) y0) x3.
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) := ((@IN a0 x3 x0) /\ (~ (@IN a0 x3 (@INSERT a0 x1 (@EMPTY a0))))) -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = True.
Definition term43 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : a0 -> real, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) (y0 y1))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 y0).
Definition term37 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> real, ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (forall y1 : a0, (@IN a0 y1 (@DIFF a0 x1 x0)) -> real_le (real_of_num (NUMERAL 0)) (y0 y1)))) -> real_le (@sum a0 x0 y0) (@sum a0 x1 y0).
Definition term84 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_mul (x0 y1) (x1 y1)) y0) x2).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) = y0) -> (y0 -> (real_le (real_of_num (NUMERAL 0)) (x2 x3)) = y1) -> ((@IN a0 x3 (@DIFF a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) -> real_le (real_of_num (NUMERAL 0)) (x2 x3)) = (y0 -> y1)) x4.
Definition term154 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> (real_le (real_of_num (NUMERAL 0)) (x0 y0)) /\ (real_le (real_of_num (NUMERAL 0)) (x2 y0)))) -> real_le (@sum a0 x1 (fun y0 : a0 => real_mul (x0 y0) (x2 y0))) (real_mul (@sum a0 x1 x0) (@sum a0 x1 x2)).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term69 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := real_le (@sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := and (real_le (x2 x0) (@sum a0 x1 x2)).
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)) x0.
Definition term54 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@DIFF a0 x0 y0)) = ((@IN a0 y1 x0) /\ (~ (@IN a0 y1 y0))).
Definition term19 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0, (y0 y1) = (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0).
Definition term18 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term115 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (x0 x1).
Definition term57 (a0 : Type') (x0 : a0 -> real) := fun y0 : real => forall y1 : a0 -> Prop, (real_mul y0 (@sum a0 y1 x0)) = (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))).
