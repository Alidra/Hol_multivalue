Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term349 (x0 : int) (x1 : int) := (int_divides x0 x1) -> (int_mul (div x1 x0) x0) = x1.
Definition term208 := fun y0 : type1551 => (forall y1 : int, forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) /\ (forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2)))).
Definition term36 (x0 : int) := forall y0 : int, (int_divides y0 x0) -> int_divides (div x0 y0) x0.
Definition term218 := fun y0 : int => forall y1 : int, (((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)).
Definition term213 := fun y0 : int => forall y1 : int, (((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)).
Definition term187 (x0 : type1551) := fun y0 : int => forall y1 : int, (~ (int_divides y1 y0)) \/ (y0 = (int_mul y1 (x0 y0 y1))).
Definition term77 := fun y0 : int => forall y1 : int, ((int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ ((~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term375 (x0 : int) (x1 : int) (x2 : int) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term337 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_divides y0 x0) \/ (~ (x0 = (int_mul y0 y1)))) x1.
Definition term42 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term378 (x0 : int) (x1 : int) := (~ (x0 = (int_mul (div x0 x1) x1))) -> x0 = (int_mul (div x0 x1) x1).
Definition term41 (x0 : int -> Prop) := ~ (all x0).
Definition term388 := (~ False) -> False.
Definition term350 (x0 : int) (x1 : int) := (~ ((int_mul (div x1 x0) x0) = x1)) -> (int_mul (div x1 x0) x0) = x1.
Definition term316 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term334 := fun y0 : int => forall y1 : int, forall y2 : int, (int_divides y1 y0) \/ (~ (y0 = (int_mul y1 y2))).
Definition term355 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term39 (x0 : int) (x1 : int) := (int_divides x0 x1) /\ (~ (int_divides (div x1 x0) x1)).
Definition term186 (x0 : type1551) := fun y0 : int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_divides y3 y1)) \/ (y1 = (int_mul y3 (y2 y3)))) y0 (x0 y0).
Definition term289 (x0 : int) := forall y0 : int, (~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0).
Definition term243 (x0 : int) := forall y0 : int, (~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0).
Definition term75 (x0 : int) := fun y0 : int => ((int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) /\ ((~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1))).
Definition term28 (x0 : int) (x1 : int) := exists y0 : int, x0 = (int_mul x1 y0).
Definition term345 (x0 : Prop) := ~ (~ x0).
Definition term178 (x0 : int) := fun y0 : int -> int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_divides y3 y1)) \/ (y1 = (int_mul y3 (y2 y3)))) x0 y0.
Definition term381 (x0 : int) (x1 : int) (x2 : int) := ~ (~ (x0 = (int_mul x1 x2))).
Definition term380 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x2 = (int_mul x1 x0)))) -> int_divides x1 x2.
Definition term131 (x0 : int) (x1 : int) := ~ (int_divides x0 x1).
Definition term353 (x0 : int) (x1 : int) := ~ ((int_mul (div x0 x1) x1) = (int_mul (div x0 x1) x1)).
Definition term377 (x0 : int) (x1 : int) := (((int_mul (div x0 x1) x1) = x0) /\ ((int_mul (div x0 x1) x1) = (int_mul (div x0 x1) x1))) -> x0 = (int_mul (div x0 x1) x1).
Definition term205 (x0 : type1551) := (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ ((fun y0 : type1551 => forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2)))) x0).
Definition term108 := fun y0 : int => forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2)).
Definition term107 := fun y0 : int => forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2))).
Definition term32 := fun y0 : int => forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2)).
Definition term60 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => x0 = (int_mul x1 y0)) x2.
Definition term376 (x0 : int) (x1 : int) := ((int_mul (div x0 x1) x1) = x0) /\ ((int_mul (div x0 x1) x1) = (int_mul (div x0 x1) x1)).
Definition term13 := (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ~ ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))).
Definition term168 := fun y0 : int => exists y1 : int -> int, forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2))).
Definition term368 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term382 (x0 : int) (x1 : int) (x2 : int) := imp (~ (~ (x0 = (int_mul x1 x2)))).
Definition term73 (x0 : int) (x1 : int) := ((int_divides x1 x0) \/ (~ (exists y0 : int, x0 = (int_mul x1 y0)))) /\ ((~ (int_divides x1 x0)) \/ (exists y0 : int, x0 = (int_mul x1 y0))).
Definition term87 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) x1.
Definition term317 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term299 (x0 : int) := (fun y0 : int => forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)) x0.
Definition term297 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) x0.
Definition term253 (x0 : int) := (fun y0 : int => forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)) x0.
Definition term251 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) x0.
Definition term111 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))) x0.
Definition term109 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) x0.
Definition term51 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0) x0.
Definition term371 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term195 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term373 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term336 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_divides y1 y0) \/ (~ (y0 = (int_mul y1 y2)))) x0.
Definition term372 (x0 : int) (x1 : int) (x2 : int) := (x1 = x0) /\ (x1 = x2).
Definition term282 (x0 : int) := fun y0 : int => (fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0.
Definition term236 (x0 : int) := fun y0 : int => (fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0.
Definition term217 (x0 : int) := forall y0 : int, (((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0)).
Definition term212 (x0 : int) := forall y0 : int, (((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0)).
Definition term63 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => x0 = (int_mul x1 y1)) y0).
Definition term47 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (int_divides y1 x0) -> int_divides (div x0 y1) x0) y0).
Definition term58 (x0 : int) (x1 : int) := ~ (exists y0 : int, x0 = (int_mul x1 y0)).
Definition term308 := and (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))).
Definition term262 := and (forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))).
Definition term220 := and (forall y0 : int, forall y1 : int, (((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0))).
Definition term120 := and (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))).
Definition term26 := and (forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)).
Definition term101 (x0 : int) := forall y0 : int, (~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term137 (x0 : int) (x1 : int) (x2 : int) := (~ (int_divides x1 x0)) \/ (x0 = (int_mul x1 x2)).
Definition term149 (x0 : int) := fun y0 : int => fun y1 : int => (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1)).
Definition term196 (x0 : Prop) (x1 : type924) := x0 /\ (exists y0 : type1551, x1 y0).
Definition term294 := (forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0).
Definition term269 (x0 : int) := (forall y0 : int, (fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0) /\ (forall y0 : int, (fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0).
Definition term248 := (forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0).
Definition term223 (x0 : int) := (forall y0 : int, (fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0) /\ (forall y0 : int, (fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0).
Definition term106 := (forall y0 : int, (fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0).
Definition term84 (x0 : int) := (forall y0 : int, (fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0) /\ (forall y0 : int, (fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0).
Definition term343 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term290 (x0 : int) := (forall y0 : int, ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) /\ (forall y0 : int, (~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0)).
Definition term244 (x0 : int) := (forall y0 : int, ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) /\ (forall y0 : int, (~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0)).
Definition term102 (x0 : int) := (forall y0 : int, (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) /\ (forall y0 : int, (~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1))).
Definition term209 := exists y0 : type1551, (forall y1 : int, forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) /\ (forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2)))).
Definition term45 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) -> int_divides (div x0 y0) x0) x1.
Definition term72 (x0 : int) (x1 : int) := and ((int_divides x1 x0) \/ (forall y0 : int, ~ (x0 = (int_mul x1 y0)))).
Definition term74 (x0 : int) (x1 : int) := ((int_divides x1 x0) \/ (forall y0 : int, ~ (x0 = (int_mul x1 y0)))) /\ ((~ (int_divides x1 x0)) \/ (exists y0 : int, x0 = (int_mul x1 y0))).
Definition term30 (x0 : int) := fun y0 : int => (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term194 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term342 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term364 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term76 (x0 : int) := forall y0 : int, ((int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) /\ ((~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1))).
Definition term275 (x0 : int) (x1 : int) := and (((int_mul (div x1 x0) x0) = x1) \/ (~ (int_divides x0 x1))).
Definition term229 (x0 : int) (x1 : int) := and (((int_mul x0 (div x1 x0)) = x1) \/ (~ (int_divides x0 x1))).
Definition term366 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term135 (x0 : int) (x1 : int) := @eq Prop ((~ (int_divides x1 x0)) \/ (exists y0 : int, x0 = (int_mul x1 y0))).
Definition term134 (x0 : int) (x1 : int) := @eq Prop ((~ (int_divides x1 x0)) \/ (exists y0 : int, (fun y1 : int => x0 = (int_mul x1 y1)) y0)).
Definition term52 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0) x0).
Definition term143 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term159 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => (~ (int_divides x2 x0)) \/ (x0 = (int_mul x2 y0))) (x1 x2).
Definition term361 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term64 (x0 : int) (x1 : int) := fun y0 : int => ~ (x0 = (int_mul x1 y0)).
Definition term207 := fun y0 : type1551 => (forall y1 : int, forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) /\ ((fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0).
Definition term362 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term173 := exists y0 : type1551, forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_divides y4 y2)) \/ (y2 = (int_mul y4 (y3 y4)))) y1 (y0 y1).
Definition term171 (x0 : type1548) := exists y0 : type1551, forall y1 : int, x0 y1 (y0 y1).
Definition term167 (x0 : int) := exists y0 : int -> int, forall y1 : int, (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 (y0 y1))).
Definition term148 (x0 : int) := exists y0 : int -> int, forall y1 : int, (fun y2 : int => fun y3 : int => (~ (int_divides y2 x0)) \/ (x0 = (int_mul y2 y3))) y1 (y0 y1).
Definition term146 (x0 : type1550) := exists y0 : int -> int, forall y1 : int, x0 y1 (y0 y1).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term270 (x0 : int) := fun y0 : int => ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0)).
Definition term224 (x0 : int) := fun y0 : int => ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0)).
Definition term96 (x0 : int) := forall y0 : int, (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1))).
Definition term359 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term346 (x0 : int) (x1 : int) := ~ (~ (int_divides x0 x1)).
Definition term154 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => fun y2 : int => (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 y2))) x1 y0.
Definition term332 (x0 : int) := fun y0 : int => forall y1 : int, (int_divides y0 x0) \/ (~ (x0 = (int_mul y0 y1))).
Definition term295 := fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0)).
Definition term249 := fun y0 : int => forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0)).
Definition term197 (x0 : Prop) (x1 : type924) := exists y0 : type1551, x0 /\ (x1 y0).
Definition term150 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1))) x1.
Definition term193 := (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (exists y0 : type1551, forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2)))).
Definition term89 (x0 : int) (x1 : int) := (fun y0 : int => (~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1))) x1.
Definition term85 (x0 : int) := fun y0 : int => (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1))).
Definition term312 := (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)).
Definition term266 := (forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)).
Definition term221 := (forall y0 : int, forall y1 : int, (((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0))).
Definition term206 (x0 : type1551) := (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (forall y0 : int, forall y1 : int, (~ (int_divides y1 y0)) \/ (y0 = (int_mul y1 (x0 y0 y1)))).
Definition term124 := (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (forall y0 : int, forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term10 := (forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0)).
Definition term215 (x0 : int) (x1 : int) := (((int_mul (div x1 x0) x0) = x1) \/ (~ (int_divides x0 x1))) /\ ((~ ((int_mul (div x1 x0) x0) = x1)) \/ (int_divides x0 x1)).
Definition term210 (x0 : int) (x1 : int) := (((int_mul x0 (div x1 x0)) = x1) \/ (~ (int_divides x0 x1))) /\ ((~ ((int_mul x0 (div x1 x0)) = x1)) \/ (int_divides x0 x1)).
Definition term298 (x0 : int) := and ((fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) x0).
Definition term252 (x0 : int) := and ((fun y0 : int => forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) x0).
Definition term110 (x0 : int) := and ((fun y0 : int => forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) x0).
Definition term139 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_divides x1 x0)) \/ (x0 = (int_mul x1 y0)).
Definition term177 (x0 : int) (x1 : int -> int) := (fun y0 : int -> int => forall y1 : int, (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 (y0 y1)))) x1.
Definition term138 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_divides x1 x0)) \/ ((fun y1 : int => x0 = (int_mul x1 y1)) y0).
Definition term307 := and (forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0).
Definition term285 (x0 : int) := and (forall y0 : int, (fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0).
Definition term261 := and (forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0).
Definition term239 (x0 : int) := and (forall y0 : int, (fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0).
Definition term119 := and (forall y0 : int, (fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0).
Definition term97 (x0 : int) := and (forall y0 : int, (fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0).
Definition term303 := @eq Prop (forall y0 : int, (forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0))).
Definition term302 := @eq Prop (forall y0 : int, ((fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0)).
Definition term281 (x0 : int) := @eq Prop (forall y0 : int, (((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0))).
Definition term280 (x0 : int) := @eq Prop (forall y0 : int, ((fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0)).
Definition term257 := @eq Prop (forall y0 : int, (forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0))).
Definition term256 := @eq Prop (forall y0 : int, ((fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0)).
Definition term235 (x0 : int) := @eq Prop (forall y0 : int, (((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0))).
Definition term234 (x0 : int) := @eq Prop (forall y0 : int, ((fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0)).
Definition term115 := @eq Prop (forall y0 : int, (forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2)))).
Definition term114 := @eq Prop (forall y0 : int, ((fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0)).
Definition term93 (x0 : int) := @eq Prop (forall y0 : int, ((int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) /\ ((~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1)))).
Definition term92 (x0 : int) := @eq Prop (forall y0 : int, ((fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0) /\ ((fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0)).
Definition term331 (x0 : int) (x1 : int) := forall y0 : int, (int_divides x1 x0) \/ (~ (x0 = (int_mul x1 y0))).
Definition term57 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term48 (x0 : int) := fun y0 : int => (int_divides y0 x0) /\ (~ (int_divides (div x0 y0) x0)).
Definition term340 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term176 (x0 : int) (x1 : int -> int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2)))) x0 x1.
Definition term267 := and ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0))).
Definition term29 (x0 : int) (x1 : int) := @eq Prop (int_divides x0 x1).
Definition term322 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ~ (x0 = (int_mul x1 y0))) x2.
Definition term348 (x0 : int) (x1 : int) := imp (int_divides x0 x1).
Definition term22 (x0 : int) := fun y0 : int => ((int_mul y0 (div x0 y0)) = x0) = (int_divides y0 x0).
Definition term17 (x0 : int) := fun y0 : int => ((int_mul (div x0 y0) y0) = x0) = (int_divides y0 x0).
Definition term202 := exists y0 : type1551, (fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0.
Definition term315 (x0 : type1551) (x1 : int) := fun y0 : int => (~ (int_divides y0 x1)) \/ (x1 = (int_mul y0 (x0 x1 y0))).
Definition term128 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 \/ (x1 y0).
Definition term330 (x0 : int) (x1 : int) := fun y0 : int => (int_divides x1 x0) \/ (~ (x0 = (int_mul x1 y0))).
Definition term153 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => fun y2 : int => (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 y2))) x1 y0.
Definition term126 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term23 (x0 : int) := forall y0 : int, ((int_mul y0 (div x0 y0)) = x0) = (int_divides y0 x0).
Definition term18 (x0 : int) := forall y0 : int, ((int_mul (div x0 y0) y0) = x0) = (int_divides y0 x0).
Definition term293 := forall y0 : int, ((fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0).
Definition term268 (x0 : int) := forall y0 : int, ((fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0).
Definition term247 := forall y0 : int, ((fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0).
Definition term222 (x0 : int) := forall y0 : int, ((fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0).
Definition term105 := forall y0 : int, ((fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0).
Definition term83 (x0 : int) := forall y0 : int, ((fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0) /\ ((fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0).
Definition term365 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term125 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term182 := @eq Prop (forall y0 : int, exists y1 : int -> int, forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2)))).
Definition term181 := @eq Prop (forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_divides y4 y2)) \/ (y2 = (int_mul y4 (y3 y4)))) y0 y1).
Definition term157 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1))).
Definition term156 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_divides y2 x0)) \/ (x0 = (int_mul y2 y3))) y0 y1).
Definition term175 (x0 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2)))) x0.
Definition term174 := fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2))).
Definition term56 (x0 : int -> Prop) := ~ (ex x0).
Definition term43 (x0 : int) := ~ (forall y0 : int, (int_divides y0 x0) -> int_divides (div x0 y0) x0).
Definition term360 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term140 (x0 : int) (x1 : int) := exists y0 : int, (~ (int_divides x1 x0)) \/ (x0 = (int_mul x1 y0)).
Definition term6 := (((~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term133 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => x0 = (int_mul x1 y1)) y0.
Definition term179 (x0 : int) := exists y0 : int -> int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_divides y3 y1)) \/ (y1 = (int_mul y3 (y2 y3)))) x0 y0.
Definition term273 (x0 : int) (x1 : int) := ((int_mul (div x1 x0) x0) = x1) \/ (~ (int_divides x0 x1)).
Definition term12 := (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term292 := forall y0 : int, (forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)).
Definition term246 := forall y0 : int, (forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)).
Definition term104 := forall y0 : int, (forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term363 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term227 (x0 : int) (x1 : int) := ((int_mul x0 (div x1 x0)) = x1) \/ (~ (int_divides x0 x1)).
Definition term158 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => fun y1 : int => (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1))) x2 (x1 x2).
Definition term160 (x0 : int) (x1 : int -> int) (x2 : int) := (~ (int_divides x2 x0)) \/ (x0 = (int_mul x2 (x1 x2))).
Definition term335 := forall y0 : int, forall y1 : int, forall y2 : int, (int_divides y1 y0) \/ (~ (y0 = (int_mul y1 y2))).
Definition term333 (x0 : int) := forall y0 : int, forall y1 : int, (int_divides y0 x0) \/ (~ (x0 = (int_mul y0 y1))).
Definition term311 := forall y0 : int, forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0).
Definition term306 := forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0)).
Definition term265 := forall y0 : int, forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0).
Definition term260 := forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0)).
Definition term219 := forall y0 : int, forall y1 : int, (((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)).
Definition term214 := forall y0 : int, forall y1 : int, (((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ ((~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)).
Definition term189 (x0 : type1551) := forall y0 : int, forall y1 : int, (~ (int_divides y1 y0)) \/ (y0 = (int_mul y1 (x0 y0 y1))).
Definition term123 := forall y0 : int, forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2)).
Definition term118 := forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2))).
Definition term78 := forall y0 : int, forall y1 : int, ((int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ ((~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term33 := forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2)).
Definition term25 := forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0).
Definition term20 := forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0).
Definition term1 := forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0.
Definition term386 (x0 : int) (x1 : int) := (~ (int_divides (div x1 x0) x1)) -> int_divides (div x1 x0) x1.
Definition term163 (x0 : int) (x1 : int -> int) := forall y0 : int, (fun y1 : int => fun y2 : int => (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 y2))) y0 (x1 y0).
Definition term339 (x0 : int) (x1 : int) := ~ (int_divides (div x1 x0) x1).
Definition term190 := fun y0 : type1551 => forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_divides y4 y2)) \/ (y2 = (int_mul y4 (y3 y4)))) y1 (y0 y1).
Definition term166 (x0 : int) := fun y0 : int -> int => forall y1 : int, (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 (y0 y1))).
Definition term165 (x0 : int) := fun y0 : int -> int => forall y1 : int, (fun y2 : int => fun y3 : int => (~ (int_divides y2 x0)) \/ (x0 = (int_mul y2 y3))) y1 (y0 y1).
Definition term351 (x0 : int) (x1 : int) := ~ ((int_mul (div x1 x0) x0) = x1).
Definition term188 (x0 : type1551) := forall y0 : int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_divides y3 y1)) \/ (y1 = (int_mul y3 (y2 y3)))) y0 (x0 y0).
Definition term279 (x0 : int) := fun y0 : int => ((fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0).
Definition term233 (x0 : int) := fun y0 : int => ((fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0) /\ ((fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0).
Definition term91 (x0 : int) := fun y0 : int => ((fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0) /\ ((fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0).
Definition term277 (x0 : int) (x1 : int) := (~ ((int_mul (div x1 x0) x0) = x1)) \/ (int_divides x0 x1).
Definition term231 (x0 : int) (x1 : int) := (~ ((int_mul x0 (div x1 x0)) = x1)) \/ (int_divides x0 x1).
Definition term127 (x0 : Prop) (x1 : int -> Prop) := x0 \/ (exists y0 : int, x1 y0).
Definition term352 (x0 : int) (x1 : int) := (~ ((int_mul (div x0 x1) x1) = (int_mul (div x0 x1) x1))) -> (int_mul (div x0 x1) x1) = (int_mul (div x0 x1) x1).
Definition term27 (x0 : int) (x1 : int) := fun y0 : int => x0 = (int_mul x1 y0).
Definition term38 (x0 : int) (x1 : int) := ~ ((int_divides x0 x1) -> int_divides (div x1 x0) x1).
Definition term2 := (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> False.
Definition term132 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => x0 = (int_mul x1 y1)) y0.
Definition term162 (x0 : int) (x1 : int -> int) := fun y0 : int => (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 (x1 y0))).
Definition term291 := fun y0 : int => (forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)).
Definition term245 := fun y0 : int => (forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)).
Definition term103 := fun y0 : int => (forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term40 (x0 : int) (x1 : int) := int_divides (div x1 x0) x1.
Definition term296 := fun y0 : int => forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0).
Definition term250 := fun y0 : int => forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0).
Definition term37 := fun y0 : int => forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0.
Definition term24 := fun y0 : int => forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0).
Definition term19 := fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0).
Definition term201 := fun y0 : type1551 => (fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0.
Definition term66 (x0 : int) (x1 : int) := or (~ (int_divides x0 x1)).
Definition term314 (x0 : type1551) (x1 : int) (x2 : int) := (~ (int_divides x2 x1)) \/ (x1 = (int_mul x2 (x0 x1 x2))).
Definition term358 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 := (((~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> ((~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term34 (x0 : int) (x1 : int) := (int_divides x0 x1) -> int_divides (div x1 x0) x1.
Definition term9 := ~ ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))).
Definition term61 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => x0 = (int_mul x1 y0)) x2).
Definition term370 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term199 := exists y0 : type1551, (forall y1 : int, forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) /\ ((fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0).
Definition term310 := forall y0 : int, (fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0.
Definition term305 := forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0.
Definition term264 := forall y0 : int, (fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0.
Definition term259 := forall y0 : int, (fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0.
Definition term122 := forall y0 : int, (fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0.
Definition term117 := forall y0 : int, (fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0.
Definition term3 := ~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0).
Definition term16 (x0 : int) (x1 : int) := int_mul (div x0 x1) x1.
Definition term274 (x0 : int) (x1 : int) := and ((fun y0 : int => ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) x1).
Definition term228 (x0 : int) (x1 : int) := and ((fun y0 : int => ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) x1).
Definition term88 (x0 : int) (x1 : int) := and ((fun y0 : int => (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) x1).
Definition term216 (x0 : int) := fun y0 : int => (((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0)).
Definition term211 (x0 : int) := fun y0 : int => (((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) /\ ((~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0)).
Definition term356 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term46 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (int_divides y0 x0) -> int_divides (div x0 y0) x0) x1).
Definition term11 := imp (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))).
Definition term184 (x0 : type1551) (x1 : int) := (fun y0 : int -> int => forall y1 : int, (~ (int_divides y1 x1)) \/ (x1 = (int_mul y1 (y0 y1)))) (x0 x1).
Definition term81 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term385 (x0 : int) (x1 : int) := (x1 = (int_mul (div x1 x0) x0)) -> int_divides (div x1 x0) x1.
Definition term161 (x0 : int) (x1 : int -> int) := fun y0 : int => (fun y1 : int => fun y2 : int => (~ (int_divides y1 x0)) \/ (x0 = (int_mul y1 y2))) y0 (x1 y0).
Definition term379 (x0 : int) (x1 : int) := ~ (x0 = (int_mul (div x0 x1) x1)).
Definition term272 (x0 : int) (x1 : int) := (fun y0 : int => ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) x1.
Definition term226 (x0 : int) (x1 : int) := (fun y0 : int => ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) x1.
Definition term323 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0.
Definition term286 (x0 : int) := and (forall y0 : int, ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))).
Definition term240 (x0 : int) := and (forall y0 : int, ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))).
Definition term98 (x0 : int) := and (forall y0 : int, (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))).
Definition term300 (x0 : int) := ((fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) x0) /\ ((fun y0 : int => forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0)) x0).
Definition term254 (x0 : int) := ((fun y0 : int => forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) x0) /\ ((fun y0 : int => forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0)) x0).
Definition term112 (x0 : int) := ((fun y0 : int => forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) x0) /\ ((fun y0 : int => forall y1 : int, (~ (int_divides y1 y0)) \/ (exists y2 : int, y0 = (int_mul y1 y2))) x0).
Definition term198 := (forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (exists y0 : type1551, (fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0).
Definition term328 (x0 : int) (x1 : int) (x2 : int) := (int_divides x1 x0) \/ (~ (x0 = (int_mul x1 x2))).
Definition term69 (x0 : int) (x1 : int) := (int_divides x1 x0) \/ (~ (exists y0 : int, x0 = (int_mul x1 y0))).
Definition term200 (x0 : type1551) := (fun y0 : type1551 => forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2)))) x0.
Definition term326 (x0 : int) (x1 : int) := @eq Prop ((int_divides x1 x0) \/ (forall y0 : int, ~ (x0 = (int_mul x1 y0)))).
Definition term325 (x0 : int) (x1 : int) := @eq Prop ((int_divides x1 x0) \/ (forall y0 : int, (fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0)).
Definition term65 (x0 : int) (x1 : int) := forall y0 : int, ~ (x0 = (int_mul x1 y0)).
Definition term180 := fun y0 : int => exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_divides y4 y2)) \/ (y2 = (int_mul y4 (y3 y4)))) y0 y1.
Definition term284 (x0 : int) := forall y0 : int, ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0)).
Definition term238 (x0 : int) := forall y0 : int, ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0)).
Definition term192 := exists y0 : type1551, forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2))).
Definition term324 (x0 : int) (x1 : int) := forall y0 : int, (fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0.
Definition term321 (x0 : int) (x1 : int) := forall y0 : int, (int_divides x1 x0) \/ ((fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0).
Definition term287 (x0 : int) := fun y0 : int => (fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0.
Definition term241 (x0 : int) := fun y0 : int => (fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0.
Definition term67 (x0 : int) (x1 : int) := (~ (int_divides x1 x0)) \/ (exists y0 : int, x0 = (int_mul x1 y0)).
Definition term271 (x0 : int) := fun y0 : int => (~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0).
Definition term225 (x0 : int) := fun y0 : int => (~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0).
Definition term367 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term320 (x0 : int) (x1 : int) := (int_divides x1 x0) \/ (forall y0 : int, (fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0).
Definition term136 (x0 : int) (x1 : int) (x2 : int) := (~ (int_divides x1 x0)) \/ ((fun y0 : int => x0 = (int_mul x1 y0)) x2).
Definition term82 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term185 (x0 : type1551) (x1 : int) := forall y0 : int, (~ (int_divides y0 x1)) \/ (x1 = (int_mul y0 (x0 x1 y0))).
Definition term164 (x0 : int) (x1 : int -> int) := forall y0 : int, (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 (x1 y0))).
Definition term276 (x0 : int) (x1 : int) := (fun y0 : int => (~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0)) x1.
Definition term230 (x0 : int) (x1 : int) := (fun y0 : int => (~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0)) x1.
Definition term21 (x0 : int) (x1 : int) := int_mul x1 (div x0 x1).
Definition term35 (x0 : int) := fun y0 : int => (int_divides y0 x0) -> int_divides (div x0 y0) x0.
Definition term301 := fun y0 : int => ((fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0).
Definition term255 := fun y0 : int => ((fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0) /\ ((fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0).
Definition term113 := fun y0 : int => ((fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0) /\ ((fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0).
Definition term341 (x0 : int) (x1 : int) := (~ (int_divides x0 x1)) -> int_divides x0 x1.
Definition term70 (x0 : int) (x1 : int) := (int_divides x1 x0) \/ (forall y0 : int, ~ (x0 = (int_mul x1 y0))).
Definition term183 (x0 : type1551) (x1 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2)))) x1 (x0 x1).
Definition term387 (x0 : int) (x1 : int) := (int_divides (div x1 x0) x1) -> False.
Definition term8 := ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term278 (x0 : int) (x1 : int) := ((fun y0 : int => ((int_mul (div x0 y0) y0) = x0) \/ (~ (int_divides y0 x0))) x1) /\ ((fun y0 : int => (~ ((int_mul (div x0 y0) y0) = x0)) \/ (int_divides y0 x0)) x1).
Definition term232 (x0 : int) (x1 : int) := ((fun y0 : int => ((int_mul y0 (div x0 y0)) = x0) \/ (~ (int_divides y0 x0))) x1) /\ ((fun y0 : int => (~ ((int_mul y0 (div x0 y0)) = x0)) \/ (int_divides y0 x0)) x1).
Definition term90 (x0 : int) (x1 : int) := ((fun y0 : int => (int_divides y0 x0) \/ (forall y1 : int, ~ (x0 = (int_mul y0 y1)))) x1) /\ ((fun y0 : int => (~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1))) x1).
Definition term15 := (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ~ ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))).
Definition term344 (x0 : int) (x1 : int) := (~ (~ (int_divides x0 x1))) -> (int_mul (div x1 x0) x0) = x1.
Definition term204 := @eq Prop ((forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (exists y0 : type1551, forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2))))).
Definition term203 := @eq Prop ((forall y0 : int, forall y1 : int, (int_divides y1 y0) \/ (forall y2 : int, ~ (y0 = (int_mul y1 y2)))) /\ (exists y0 : type1551, (fun y1 : type1551 => forall y2 : int, forall y3 : int, (~ (int_divides y3 y2)) \/ (y2 = (int_mul y3 (y1 y2 y3)))) y0)).
Definition term374 (x0 : int) (x1 : int) (x2 : int) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term172 := forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_divides y4 y2)) \/ (y2 = (int_mul y4 (y3 y4)))) y0 y1.
Definition term170 (x0 : type1548) := forall y0 : int, exists y1 : int -> int, x0 y0 y1.
Definition term169 := forall y0 : int, exists y1 : int -> int, forall y2 : int, (~ (int_divides y2 y0)) \/ (y0 = (int_mul y2 (y1 y2))).
Definition term147 (x0 : int) := forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_divides y2 x0)) \/ (x0 = (int_mul y2 y3))) y0 y1.
Definition term145 (x0 : type1550) := forall y0 : int, exists y1 : int, x0 y0 y1.
Definition term142 (x0 : int) := forall y0 : int, exists y1 : int, (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1)).
Definition term384 (x0 : int) (x1 : int) (x2 : int) := (x2 = (int_mul x1 x0)) -> int_divides x1 x2.
Definition term327 (x0 : int) (x1 : int) (x2 : int) := (int_divides x1 x0) \/ ((fun y0 : int => ~ (x0 = (int_mul x1 y0))) x2).
Definition term50 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (int_divides y2 y1) -> int_divides (div y1 y2) y1) y0).
Definition term44 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (int_divides y1 x0) -> int_divides (div x0 y1) x0) y0).
Definition term383 (x0 : int) (x1 : int) (x2 : int) := imp (x0 = (int_mul x1 x2)).
Definition term86 (x0 : int) := fun y0 : int => (~ (int_divides y0 x0)) \/ (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term55 := exists y0 : int, exists y1 : int, (int_divides y1 y0) /\ (~ (int_divides (div y0 y1) y0)).
Definition term71 (x0 : int) (x1 : int) := and ((int_divides x1 x0) \/ (~ (exists y0 : int, x0 = (int_mul x1 y0)))).
Definition term155 (x0 : int) := fun y0 : int => exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_divides y2 x0)) \/ (x0 = (int_mul y2 y3))) y0 y1.
Definition term141 (x0 : int) := fun y0 : int => exists y1 : int, (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1)).
Definition term354 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term129 (x0 : int) (x1 : int) := (~ (int_divides x1 x0)) \/ (exists y0 : int, (fun y1 : int => x0 = (int_mul x1 y1)) y0).
Definition term191 := fun y0 : type1551 => forall y1 : int, forall y2 : int, (~ (int_divides y2 y1)) \/ (y1 = (int_mul y2 (y0 y1 y2))).
Definition term369 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term54 := fun y0 : int => exists y1 : int, (int_divides y1 y0) /\ (~ (int_divides (div y0 y1) y0)).
Definition term31 (x0 : int) := forall y0 : int, (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term357 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term152 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (~ (int_divides x1 x0)) \/ (x0 = (int_mul x1 y0))) x2.
Definition term144 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term68 (x0 : int) (x1 : int) := or (int_divides x0 x1).
Definition term338 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_divides x1 x0) \/ (~ (x0 = (int_mul x1 y0)))) x2.
Definition term4 := (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)) -> (forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) -> ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) = (int_divides y1 y0)) /\ (forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0))) -> False.
Definition term288 (x0 : int) := forall y0 : int, (fun y1 : int => (~ ((int_mul (div x0 y1) y1) = x0)) \/ (int_divides y1 x0)) y0.
Definition term283 (x0 : int) := forall y0 : int, (fun y1 : int => ((int_mul (div x0 y1) y1) = x0) \/ (~ (int_divides y1 x0))) y0.
Definition term242 (x0 : int) := forall y0 : int, (fun y1 : int => (~ ((int_mul y1 (div x0 y1)) = x0)) \/ (int_divides y1 x0)) y0.
Definition term237 (x0 : int) := forall y0 : int, (fun y1 : int => ((int_mul y1 (div x0 y1)) = x0) \/ (~ (int_divides y1 x0))) y0.
Definition term100 (x0 : int) := forall y0 : int, (fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0.
Definition term95 (x0 : int) := forall y0 : int, (fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0.
Definition term49 (x0 : int) := exists y0 : int, (int_divides y0 x0) /\ (~ (int_divides (div x0 y0) x0)).
Definition term62 (x0 : int) (x1 : int) (x2 : int) := ~ (x0 = (int_mul x1 x2)).
Definition term309 := fun y0 : int => (fun y1 : int => forall y2 : int, (~ ((int_mul (div y1 y2) y2) = y1)) \/ (int_divides y2 y1)) y0.
Definition term304 := fun y0 : int => (fun y1 : int => forall y2 : int, ((int_mul (div y1 y2) y2) = y1) \/ (~ (int_divides y2 y1))) y0.
Definition term263 := fun y0 : int => (fun y1 : int => forall y2 : int, (~ ((int_mul y2 (div y1 y2)) = y1)) \/ (int_divides y2 y1)) y0.
Definition term258 := fun y0 : int => (fun y1 : int => forall y2 : int, ((int_mul y2 (div y1 y2)) = y1) \/ (~ (int_divides y2 y1))) y0.
Definition term121 := fun y0 : int => (fun y1 : int => forall y2 : int, (~ (int_divides y2 y1)) \/ (exists y3 : int, y1 = (int_mul y2 y3))) y0.
Definition term116 := fun y0 : int => (fun y1 : int => forall y2 : int, (int_divides y2 y1) \/ (forall y3 : int, ~ (y1 = (int_mul y2 y3)))) y0.
Definition term99 (x0 : int) := fun y0 : int => (fun y1 : int => (~ (int_divides y1 x0)) \/ (exists y2 : int, x0 = (int_mul y1 y2))) y0.
Definition term94 (x0 : int) := fun y0 : int => (fun y1 : int => (int_divides y1 x0) \/ (forall y2 : int, ~ (x0 = (int_mul y1 y2)))) y0.
Definition term318 (x0 : Prop) (x1 : int -> Prop) := x0 \/ (forall y0 : int, x1 y0).
Definition term329 (x0 : int) (x1 : int) := fun y0 : int => (int_divides x1 x0) \/ ((fun y1 : int => ~ (x0 = (int_mul x1 y1))) y0).
Definition term14 := imp (~ (forall y0 : int, forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0)).
Definition term151 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => fun y1 : int => (~ (int_divides y0 x0)) \/ (x0 = (int_mul y0 y1))) x1 x2.
Definition term130 (x0 : int) (x1 : int) := exists y0 : int, (~ (int_divides x1 x0)) \/ ((fun y1 : int => x0 = (int_mul x1 y1)) y0).
Definition term53 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (int_divides y2 y1) -> int_divides (div y1 y2) y1) y0).
Definition term313 := ((forall y0 : int, forall y1 : int, ((int_mul y1 (div y0 y1)) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (~ ((int_mul y1 (div y0 y1)) = y0)) \/ (int_divides y1 y0))) /\ ((forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) \/ (~ (int_divides y1 y0))) /\ (forall y0 : int, forall y1 : int, (~ ((int_mul (div y0 y1) y1) = y0)) \/ (int_divides y1 y0))).
Definition term319 (x0 : Prop) (x1 : int -> Prop) := forall y0 : int, x0 \/ (x1 y0).
Definition term347 (x0 : int) (x1 : int) := imp (~ (~ (int_divides x0 x1))).
Definition term59 (x0 : int) (x1 : int) := forall y0 : int, ~ ((fun y1 : int => x0 = (int_mul x1 y1)) y0).
