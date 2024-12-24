Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ~ ((fun y0 : a0 => (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))) x2).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ~ ((fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) x2).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (@IN a0 y0 x0) \/ (x0 = (@EMPTY a0)).
Definition term137 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_le x0 x1).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) := ((exists y0 : a0, @IN a0 y0 x0) \/ (x0 = (@EMPTY a0))) /\ ((forall y0 : a0, ~ (@IN a0 y0 x0)) \/ (~ (x0 = (@EMPTY a0)))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0.
Definition term288 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (~ (@IN a0 (x0 x1) x1)) -> @IN a0 (x0 x1) x1.
Definition term179 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0.
Definition term259 := (~ False) -> False.
Definition term223 (a0 : Type') (x0 : type684 a0) := fun y0 : a0 -> Prop => (@IN a0 (x0 y0) y0) \/ (y0 = (@EMPTY a0)).
Definition term27 := imp (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) x2.
Definition term189 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => @IN a0 y1 x0) y0) \/ (x0 = (@EMPTY a0)).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (@FINITE a0 x0)) \/ (exists y0 : a0, (fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0).
Definition term252 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (real_le x0 y0)) x1.
Definition term221 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (@IN a0 (x0 x1) x1) \/ (x1 = (@EMPTY a0)).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (~ (@FINITE a0 x0)) \/ ((fun y0 : a0 => ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))))) x2).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term262 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := @eq Prop ((~ (@IN a0 x2 x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (x1 x2))).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1)))).
Definition term266 (x0 : Prop) := ~ (~ x0).
Definition term281 := real_of_num (NUMERAL 0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := imp (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))).
Definition term290 (a0 : Type') (x0 : a0 -> real) (x1 : type684 a0) (x2 : a0 -> Prop) := (@IN a0 (x1 x2) x2) -> real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2)).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ~ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term229 (a0 : Type') := and (exists y0 : type684 a0, forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (x0 = (@EMPTY a0))).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := or ((@IN a0 x2 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 x2)))).
Definition term294 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := (~ (~ (real_lt (real_of_num (NUMERAL 0)) (x0 x1)))) -> ~ (@IN a0 x1 x2).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0))) \/ (~ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term253 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 (x0 y0) y0) \/ (y0 = (@EMPTY a0))) x1.
Definition term186 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0))).
Definition term282 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (~ (real_le (real_of_num (NUMERAL 0)) (x0 x1))) -> real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term17 (x0 : Prop) := (~ x0) -> False.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (~ (@FINITE a0 x0)) \/ (((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))))).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> False.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0).
Definition term298 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := (real_lt (real_of_num (NUMERAL 0)) (x0 x1)) -> ~ (@IN a0 x1 x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := imp (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term308 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (~ (y0 = (@EMPTY a0))) -> (forall y1 : a0, (@IN a0 y1 y0) -> real_lt (real_of_num (NUMERAL 0)) (x0 y1)) -> (~ ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1)))))) -> (forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) -> (forall y1 : a0 -> Prop, (exists y2 : a0, @IN a0 y2 y1) = (~ (y1 = (@EMPTY a0)))) -> False) x1.
Definition term192 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => @IN a0 y1 x0) y0).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := or (exists y0 : a0, (fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ~ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term163 (a0 : Type') := forall y0 : a0 -> Prop, ((exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) /\ ((forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term52 (a0 : Type') := fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (exists y0 : a0, (fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0) \/ (forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term54 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> real_le x0 y0.
Definition term159 (a0 : Type') (x0 : a0 -> Prop) := and ((exists y0 : a0, @IN a0 y0 x0) \/ (x0 = (@EMPTY a0))).
Definition term264 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) \/ (x0 = (@EMPTY a0))) x1.
Definition term194 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, @IN a0 y0 x0) \/ (x0 = (@EMPTY a0))).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => @IN a0 y1 x0) y0) \/ (x0 = (@EMPTY a0))).
Definition term230 (a0 : Type') := (exists y0 : type684 a0, forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := and (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term249 (a0 : Type') := exists y0 : type684 a0, (forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) /\ (forall y1 : a0 -> Prop, (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))).
Definition term263 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) (x0 x1)) \/ (~ (@IN a0 x1 x2))).
Definition term170 (a0 : Type') := fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0)).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => @IN a0 y0 x0) x1.
Definition term303 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := @eq Prop ((x1 = (@EMPTY a0)) \/ (@IN a0 (x0 x1) x1)).
Definition term178 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, ((exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) /\ ((forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0))))).
Definition term75 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) := and ((exists y0 : a0, @IN a0 y0 x0) \/ (~ (~ (x0 = (@EMPTY a0))))).
Definition term10 (a0 : Type') := (forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y1 y0)) -> forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((forall y2 : a0, (@IN a0 y2 y0) -> real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (exists y2 : a0, (@IN a0 y2 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (y1 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 y1).
Definition term226 (a0 : Type') := fun y0 : type684 a0 => forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 => (@IN a0 y3 y2) \/ (y2 = (@EMPTY a0))) y1 (y0 y1).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := (~ (exists y0 : a0, @IN a0 y0 x0)) \/ (~ (x0 = (@EMPTY a0))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (x0 = (@EMPTY a0))).
Definition term296 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := imp (~ (~ (real_lt (real_of_num (NUMERAL 0)) (x0 x1)))).
Definition term26 (a0 : Type') := ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term300 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (@IN a0 (x0 x1) x1) -> ~ (@IN a0 (x0 x1) x1).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term255 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ (real_le (real_of_num (NUMERAL 0)) (x0 x1)).
Definition term309 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 x1).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => ((fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1)))).
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := (~ (@FINITE a0 x1)) \/ (((@IN a0 x0 x1) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x2 x0)))) \/ (forall y0 : a0, (~ (@IN a0 y0 x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x2 y0))))).
Definition term257 (x0 : Prop) := (~ x0) -> x0.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (fun y0 : a0 -> real => ((@FINITE a0 x0) /\ ((forall y1 : a0, (@IN a0 y1 x0) -> real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (exists y1 : a0, (@IN a0 y1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y1))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 y0)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 x0)) x1.
Definition term275 (x0 : real) (x1 : real) := @eq Prop ((real_le x0 x1) \/ (~ (real_lt x0 x1))).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((fun y0 : a0 => (@IN a0 y0 x1) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x2 y0)))) x0) \/ (forall y0 : a0, (~ (@IN a0 y0 x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x2 y0)))).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, @IN a0 y0 x0).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1)))).
Definition term197 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((fun y0 : a0 => @IN a0 y0 x1) x0) \/ (x1 = (@EMPTY a0)).
Definition term204 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term276 (x0 : real) (x1 : real) := (~ (~ (real_lt x0 x1))) -> real_le x0 x1.
Definition term225 (a0 : Type') (x0 : type684 a0) := forall y0 : a0 -> Prop, (@IN a0 (x0 y0) y0) \/ (y0 = (@EMPTY a0)).
Definition term141 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1).
Definition term57 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := or (~ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0).
Definition term228 (a0 : Type') := exists y0 : type684 a0, forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0)).
Definition term209 (a0 : Type') := exists y0 : type684 a0, forall y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 => (@IN a0 y3 y2) \/ (y2 = (@EMPTY a0))) y1 (y0 y1).
Definition term207 (a0 : Type') (x0 : type672 a0) := exists y0 : type684 a0, forall y1 : a0 -> Prop, x0 y1 (y0 y1).
Definition term222 (a0 : Type') (x0 : type684 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => fun y2 : a0 => (@IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0 (x0 y0).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term274 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x0 x1)) \/ (real_le x0 x1)).
Definition term286 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (~ (x1 = (@EMPTY a0))) -> @IN a0 (x0 x1) x1.
Definition term53 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_le x0 x1.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term301 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (x1 = (@EMPTY a0)) \/ (@IN a0 (x0 x1) x1).
Definition term28 (a0 : Type') := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, @IN a0 y0 x0).
Definition term287 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := @IN a0 (x0 x1) x1.
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@IN a0 x0 x1) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x2 x0)))) \/ (forall y0 : a0, (~ (@IN a0 y0 x1)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x2 y0)))).
Definition term198 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) \/ (x1 = (@EMPTY a0)).
Definition term138 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (real_le x0 y0).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => @IN a0 y0 x0) x1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, ~ (@IN a0 y0 x0)) \/ (~ (x0 = (@EMPTY a0))).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0.
Definition term190 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => @IN a0 y1 x0) y0.
Definition term299 (a0 : Type') (x0 : a0 -> real) (x1 : type684 a0) (x2 : a0 -> Prop) := (real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2))) -> ~ (@IN a0 (x1 x2) x2).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => ~ ((fun y1 : a0 => (@IN a0 y1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))) y0).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => ~ ((fun y1 : a0 => (@IN a0 y1 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y1)) y0).
Definition term246 (a0 : Type') (x0 : type684 a0) := (forall y0 : a0 -> Prop, (@IN a0 (x0 y0) y0) \/ (y0 = (@EMPTY a0))) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term187 (a0 : Type') := (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (~ (@IN a0 x2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 x2))).
Definition term293 (a0 : Type') (x0 : a0 -> real) (x1 : type684 a0) (x2 : a0 -> Prop) := ~ (real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 x2).
Definition term184 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0.
Definition term235 (a0 : Type') := (exists y0 : type684 a0, (fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq Prop ((exists y0 : a0, (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0) \/ (forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 x2))).
Definition term176 (a0 : Type') := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0) /\ ((fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term248 (a0 : Type') := fun y0 : type684 a0 => (forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) /\ (forall y1 : a0 -> Prop, (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))).
Definition term46 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (~ (y1 = (@EMPTY a0))) -> (forall y2 : a0, (@IN a0 y2 y1) -> real_lt (real_of_num (NUMERAL 0)) (y0 y2)) -> (~ ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2)))))) -> (forall y2 : real, forall y3 : real, (real_lt y2 y3) -> real_le y2 y3) -> ~ (forall y2 : a0 -> Prop, (exists y3 : a0, @IN a0 y3 y2) = (~ (y2 = (@EMPTY a0)))).
Definition term45 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (~ (y1 = (@EMPTY a0))) -> (forall y2 : a0, (@IN a0 y2 y1) -> real_lt (real_of_num (NUMERAL 0)) (y0 y2)) -> (~ ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2)))))) -> (forall y2 : real, forall y3 : real, (real_lt y2 y3) -> real_le y2 y3) -> (forall y2 : a0 -> Prop, (exists y3 : a0, @IN a0 y3 y2) = (~ (y2 = (@EMPTY a0)))) -> False.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ((@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term215 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 -> Prop => fun y2 : a0 => (@IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) x0 y0.
Definition term236 (a0 : Type') := exists y0 : type684 a0, ((fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0) /\ (forall y1 : a0 -> Prop, (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))).
Definition term239 (a0 : Type') := exists y0 : type684 a0, (fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x0).
Definition term181 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0)).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq Prop ((~ (@FINITE a0 x0)) \/ (exists y0 : a0, ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1)))))).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq Prop ((~ (@FINITE a0 x0)) \/ (exists y0 : a0, (fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0)).
Definition term273 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term218 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, exists y1 : a0, (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0))).
Definition term217 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, exists y1 : a0, (fun y2 : a0 -> Prop => fun y3 : a0 => (@IN a0 y3 y2) \/ (y2 = (@EMPTY a0))) y0 y1).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))) x2.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, ((fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1)))).
Definition term123 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term44 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (~ (y0 = (@EMPTY a0))) -> (forall y1 : a0, (@IN a0 y1 y0) -> real_lt (real_of_num (NUMERAL 0)) (x0 y1)) -> (~ ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1)))))) -> (forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) -> ~ (forall y1 : a0 -> Prop, (exists y2 : a0, @IN a0 y2 y1) = (~ (y1 = (@EMPTY a0)))).
Definition term43 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (~ (y0 = (@EMPTY a0))) -> (forall y1 : a0, (@IN a0 y1 y0) -> real_lt (real_of_num (NUMERAL 0)) (x0 y1)) -> (~ ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1)))))) -> (forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) -> (forall y1 : a0 -> Prop, (exists y2 : a0, @IN a0 y2 y1) = (~ (y1 = (@EMPTY a0)))) -> False.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (~ (@FINITE a0 x0)) \/ (((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))))).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => @IN a0 y1 x0) y0.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 x2).
Definition term185 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0.
Definition term180 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0.
Definition term122 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term240 (a0 : Type') := and (exists y0 : type684 a0, (fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := or (~ (@FINITE a0 x0)).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))) x2.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (exists y0 : a0, @IN a0 y0 x0).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => fun y1 : a0 => (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x0 x1.
Definition term256 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term245 (a0 : Type') (x0 : type684 a0) := ((fun y0 : type684 a0 => forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) x0) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term243 (a0 : Type') (x0 : type684 a0) := and ((fun y0 : type684 a0 => forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) x0).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (@FINITE a0 x0)) \/ ((exists y0 : a0, (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))).
Definition term270 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (~ (real_lt (real_of_num (NUMERAL 0)) (x0 x1))) -> real_lt (real_of_num (NUMERAL 0)) (x0 x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term234 (a0 : Type') (x0 : type162 a0) (x1 : Prop) := exists y0 : type684 a0, (x0 y0) /\ x1.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))) x2.
Definition term140 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1).
Definition term56 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term25 (a0 : Type') := (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term279 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term251 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1)) x0.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term307 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (~ (y1 = (@EMPTY a0))) -> (forall y2 : a0, (@IN a0 y2 y1) -> real_lt (real_of_num (NUMERAL 0)) (y0 y2)) -> (~ ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2)))))) -> (forall y2 : real, forall y3 : real, (real_lt y2 y3) -> real_le y2 y3) -> (forall y2 : a0 -> Prop, (exists y3 : a0, @IN a0 y3 y2) = (~ (y2 = (@EMPTY a0)))) -> False) x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((forall y2 : a0, (@IN a0 y2 y0) -> real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (exists y2 : a0, (@IN a0 y2 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (y1 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 y1)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y1 y0)) x0.
Definition term172 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x0.
Definition term55 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_le x0 y0.
Definition term267 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ (@IN a0 x0 x1)).
Definition term227 (a0 : Type') := fun y0 : type684 a0 => forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => @IN a0 y0 x0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y1 y0)) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 x1).
Definition term168 (a0 : Type') := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0) /\ ((fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0).
Definition term260 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> @IN a0 x0 x1.
Definition term171 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0))).
Definition term177 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0) /\ ((fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0)).
Definition term219 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 => (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x1 (x0 x1).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (~ (@FINITE a0 x0)) \/ ((fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (((@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> ((@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term162 (a0 : Type') := fun y0 : a0 -> Prop => ((exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) /\ ((forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> False.
Definition term292 (a0 : Type') (x0 : a0 -> real) (x1 : type684 a0) (x2 : a0 -> Prop) := (~ (real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2)))) -> real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2)).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (~ (@FINITE a0 x0)) \/ ((fun y1 : a0 => ((@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) \/ (forall y2 : a0, (~ (@IN a0 y2 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y2))))) y0).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (@FINITE a0 x0)) \/ (exists y0 : a0, ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 x1).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) := or (forall y0 : a0, ~ (@IN a0 y0 x0)).
Definition term269 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term271 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ (real_lt (real_of_num (NUMERAL 0)) (x0 x1)).
Definition term311 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y0) -> real_lt (real_of_num (NUMERAL 0)) (y1 y2)))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 y1).
Definition term48 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (~ (y1 = (@EMPTY a0))) -> (forall y2 : a0, (@IN a0 y2 y1) -> real_lt (real_of_num (NUMERAL 0)) (y0 y2)) -> (~ ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2)))))) -> (forall y2 : real, forall y3 : real, (real_lt y2 y3) -> real_le y2 y3) -> ~ (forall y2 : a0 -> Prop, (exists y3 : a0, @IN a0 y3 y2) = (~ (y2 = (@EMPTY a0)))).
Definition term47 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (~ (y1 = (@EMPTY a0))) -> (forall y2 : a0, (@IN a0 y2 y1) -> real_lt (real_of_num (NUMERAL 0)) (y0 y2)) -> (~ ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2)))))) -> (forall y2 : real, forall y3 : real, (real_lt y2 y3) -> real_le y2 y3) -> (forall y2 : a0 -> Prop, (exists y3 : a0, @IN a0 y3 y2) = (~ (y2 = (@EMPTY a0)))) -> False.
Definition term9 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> real, ((@FINITE a0 y0) /\ ((forall y2 : a0, (@IN a0 y2 y0) -> real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (exists y2 : a0, (@IN a0 y2 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (y1 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 y1).
Definition term0 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> real_le (real_of_num (NUMERAL 0)) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y2))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y1 y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term306 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) -> False.
Definition term247 (a0 : Type') := fun y0 : type684 a0 => ((fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0) /\ (forall y1 : a0 -> Prop, (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x0) /\ ((fun y0 : a0 -> Prop => (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))) x0).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => @IN a0 y1 x0) y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term265 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (~ (~ (@IN a0 x2 x0))) -> real_lt (real_of_num (NUMERAL 0)) (x1 x2).
Definition term20 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term233 (a0 : Type') (x0 : type162 a0) (x1 : Prop) := (exists y0 : type684 a0, x0 y0) /\ x1.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term157 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, @IN a0 y0 x0) \/ (x0 = (@EMPTY a0)).
Definition term289 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := ~ (@IN a0 (x0 x1) x1).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (fun y1 : a0 => (@IN a0 y1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y1)))) y0.
Definition term277 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term202 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0, (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0)).
Definition term302 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := @eq Prop ((@IN a0 (x0 x1) x1) \/ (x1 = (@EMPTY a0))).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, ~ ((fun y1 : a0 => (@IN a0 y1 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y1)) y0).
Definition term166 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) /\ (x1 y0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => ((@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y1 : a0, (~ (@IN a0 y1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))))) x2.
Definition term244 (a0 : Type') (x0 : type684 a0) := and (forall y0 : a0 -> Prop, (@IN a0 (x0 y0) y0) \/ (y0 = (@EMPTY a0))).
Definition term183 (a0 : Type') := and (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) \/ (y0 = (@EMPTY a0))).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) := ((exists y0 : a0, @IN a0 y0 x0) \/ (~ (~ (x0 = (@EMPTY a0))))) /\ ((~ (exists y0 : a0, @IN a0 y0 x0)) \/ (~ (x0 = (@EMPTY a0)))).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((fun y0 : a0 => @IN a0 y0 x0) x1).
Definition term237 (a0 : Type') (x0 : type684 a0) := (fun y0 : type684 a0 => forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) x0.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ~ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term304 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (~ (@IN a0 (x0 x1) x1)) -> x1 = (@EMPTY a0).
Definition term280 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (real_lt (real_of_num (NUMERAL 0)) (x0 x1)) -> real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term272 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (real_lt x0 x1)).
Definition term42 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (~ (y0 = (@EMPTY a0))) -> (forall y1 : a0, (@IN a0 y1 y0) -> real_lt (real_of_num (NUMERAL 0)) (x0 y1)) -> (~ ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1)))))) -> (forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) -> ~ (forall y1 : a0 -> Prop, (exists y2 : a0, @IN a0 y2 y1) = (~ (y1 = (@EMPTY a0)))).
Definition term41 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (~ (y0 = (@EMPTY a0))) -> (forall y1 : a0, (@IN a0 y1 y0) -> real_lt (real_of_num (NUMERAL 0)) (x0 y1)) -> (~ ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1)))))) -> (forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_le y1 y2) -> (forall y1 : a0 -> Prop, (exists y2 : a0, @IN a0 y2 y1) = (~ (y1 = (@EMPTY a0)))) -> False.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term139 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (real_le x0 y0).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := or ((fun y0 : a0 => (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) x2).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (~ (@IN a0 x2 x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (x1 x2)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) x2.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term169 (a0 : Type') := (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0) /\ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (forall y2 : a0, ~ (@IN a0 y2 y1)) \/ (~ (y1 = (@EMPTY a0)))) y0).
Definition term216 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0, (fun y2 : a0 -> Prop => fun y3 : a0 => (@IN a0 y3 y2) \/ (y2 = (@EMPTY a0))) y0 y1.
Definition term297 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := imp (real_lt (real_of_num (NUMERAL 0)) (x0 x1)).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => @IN a0 y1 x0) y0) \/ (x0 = (@EMPTY a0)).
Definition term29 (a0 : Type') := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (@IN a0 y0 x0).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 => (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0))) x0.
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0)))) x0.
Definition term182 (a0 : Type') := and (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, @IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> ~ (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) := (~ (x0 = (@EMPTY a0))) -> x0 = (@EMPTY a0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (((@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False) -> (@FINITE a0 x0) -> (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (exists y0 : a0, (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))) \/ (forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (@IN a0 y0 x0).
Definition term242 (a0 : Type') := @eq Prop ((exists y0 : type684 a0, forall y1 : a0 -> Prop, (@IN a0 (y0 y1) y1) \/ (y1 = (@EMPTY a0))) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0))))).
Definition term241 (a0 : Type') := @eq Prop ((exists y0 : type684 a0, (fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0) /\ (forall y0 : a0 -> Prop, (forall y1 : a0, ~ (@IN a0 y1 y0)) \/ (~ (y0 = (@EMPTY a0))))).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (x0 = (@EMPTY a0))) -> (forall y0 : a0, (@IN a0 y0 x0) -> real_lt (real_of_num (NUMERAL 0)) (x1 y0)) -> (~ ((@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)))))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> (forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0)))) -> False.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (x1 y0)).
Definition term238 (a0 : Type') := fun y0 : type684 a0 => (fun y1 : type684 a0 => forall y2 : a0 -> Prop, (@IN a0 (y1 y2) y2) \/ (y2 = (@EMPTY a0))) y0.
Definition term196 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) := or (~ (exists y0 : a0, @IN a0 y0 x0)).
Definition term224 (a0 : Type') (x0 : type684 a0) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => fun y2 : a0 => (@IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) y0 (x0 y0).
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term283 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (real_le (real_of_num (NUMERAL 0)) (x0 x1)) -> False.
Definition term295 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ (~ (real_lt (real_of_num (NUMERAL 0)) (x0 x1))).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term214 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 -> Prop => fun y2 : a0 => (@IN a0 y2 y1) \/ (y1 = (@EMPTY a0))) x0 y0.
Definition term310 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> real, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x0) -> real_lt (real_of_num (NUMERAL 0)) (y0 y1)))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 y0).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> real, ((@FINITE a0 x0) /\ ((forall y1 : a0, (@IN a0 y1 x0) -> real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (exists y1 : a0, (@IN a0 y1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (y0 y1))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 x0 y0).
Definition term2 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> real_le (real_of_num (NUMERAL 0)) (x0 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (real_lt (real_of_num (NUMERAL 0)) (x0 y1))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum a0 y0 x0).
Definition term291 (a0 : Type') (x0 : a0 -> real) (x1 : type684 a0) (x2 : a0 -> Prop) := real_lt (real_of_num (NUMERAL 0)) (x0 (x1 x2)).
Definition term210 (a0 : Type') := fun y0 : a0 -> Prop => fun y1 : a0 => (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := exists y0 : a0, (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0))).
Definition term203 (a0 : Type') := forall y0 : a0 -> Prop, exists y1 : a0, (@IN a0 y1 y0) \/ (y0 = (@EMPTY a0)).
Definition term200 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) \/ (x0 = (@EMPTY a0)).
Definition term220 (a0 : Type') (x0 : type684 a0) (x1 : a0 -> Prop) := (fun y0 : a0 => (@IN a0 y0 x1) \/ (x1 = (@EMPTY a0))) (x0 x1).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => @IN a0 y1 x0) y0).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, ~ ((fun y1 : a0 => (@IN a0 y1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y1))) y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, @IN a0 y0 x0.
Definition term205 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, @IN a0 y0 x0) \/ (~ (~ (x0 = (@EMPTY a0)))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => @IN a0 y1 x0) y0) \/ (x0 = (@EMPTY a0)).
Definition term284 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) -> ~ (x0 = (@EMPTY a0)).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := or (exists y0 : a0, (@IN a0 y0 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (x1 y0)))).
Definition term167 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, x0 y0) /\ (forall y0 : a0 -> Prop, x1 y0).
Definition term261 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := (real_lt (real_of_num (NUMERAL 0)) (x0 x1)) \/ (~ (@IN a0 x1 x2)).
Definition term70 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_lt (real_of_num (NUMERAL 0)) (x0 x1).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ~ ((@IN a0 x2 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 x2)).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (~ (@FINITE a0 x0)) \/ (~ ((forall y0 : a0, (@IN a0 y0 x0) -> real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 y0))))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 x2)).
Definition term285 (x0 : Prop) := x0 -> ~ x0.
Definition term208 (a0 : Type') := forall y0 : a0 -> Prop, exists y1 : a0, (fun y2 : a0 -> Prop => fun y3 : a0 => (@IN a0 y3 y2) \/ (y2 = (@EMPTY a0))) y0 y1.
Definition term206 (a0 : Type') (x0 : type672 a0) := forall y0 : a0 -> Prop, exists y1 : a0, x0 y0 y1.
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ~ ((@IN a0 x2 x0) /\ (real_lt (real_of_num (NUMERAL 0)) (x1 x2))).
Definition term278 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
Definition term268 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (~ (@IN a0 x0 x1))).
