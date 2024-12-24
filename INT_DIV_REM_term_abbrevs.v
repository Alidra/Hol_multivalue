Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) -> int_le x0 y0) x1.
Definition term67 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))) x1.
Definition term19 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (exists y2 : int, (x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> (div x0 y0) = y1) x1.
Definition term37 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term9 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = (int_add (int_mul x1 x3) x2)) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x3))).
Definition term78 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> (div x0 x1) = y0) x2.
Definition term34 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ ((int_of_num (NUMERAL 0)) = x0).
Definition term23 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term42 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term85 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term98 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, ((int_add (int_mul x2 (rem (div x0 x2) x1)) (rem x0 x2)) = (int_add (int_mul (rem (div x0 x2) x1) x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2))).
Definition term11 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (x0 = (int_add (int_mul x1 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2))).
Definition term22 := int_of_num (NUMERAL 0).
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> (div x0 y0) = y1) x1.
Definition term86 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) = True.
Definition term57 (x0 : int) := (~ ((int_of_num (NUMERAL 0)) = x0)) -> ((int_of_num (NUMERAL 0)) = x0) = False.
Definition term77 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) x0.
Definition term61 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) -> int_le y0 y1) x0.
Definition term29 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = ((int_lt y0 y1) \/ (y0 = y1))) x0.
Definition term100 (x0 : int) (x1 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (rem (div x0 x1) y0) = (div (rem x0 (int_mul x1 y0)) x1).
Definition term65 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))) x0.
Definition term18 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (exists y3 : int, (y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2) x0.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2) x0.
Definition term94 (x0 : int) (x1 : int) (x2 : int) := int_mul x1 (rem (div x0 x1) x2).
Definition term35 := int_lt (int_of_num (NUMERAL 0)).
Definition term25 (x0 : int) := (fun y0 : int => (rem (int_of_num (NUMERAL 0)) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term31 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = ((int_lt x0 y0) \/ (x0 = y0))) x1.
Definition term62 (x0 : int) := forall y0 : int, (int_lt x0 y0) -> int_le x0 y0.
Definition term84 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term60 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x2) -> (rem (div x0 x2) x1) = (div (rem x0 (int_mul x2 x1)) x2).
Definition term40 := @eq int (int_of_num (NUMERAL 0)).
Definition term68 (x0 : int) (x1 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1)).
Definition term48 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
Definition term80 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term72 (x0 : int) (x1 : int) := (int_lt x0 x1) -> (int_le x0 x1) = True.
Definition term74 (x0 : int) (x1 : int) (x2 : int) := div (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term13 (x0 : int) (x1 : int) (x2 : int) := (exists y0 : int, (x0 = (int_add (int_mul x2 x1) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) -> (div x0 x1) = x2.
Definition term46 (x0 : int) (x1 : int) (x2 : int) := @eq int (rem (div x0 x1) x2).
Definition term88 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_lt (rem x0 x1) (int_abs x1)) = True.
Definition term36 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term81 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term59 (x0 : int) := imp (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term64 (x0 : int) (x1 : int) := (int_lt x0 x1) -> int_le x0 x1.
Definition term99 (x0 : int) (x1 : int) (x2 : int) := fun y0 : int => ((int_add (int_mul x2 (rem (div x0 x2) x1)) (rem x0 x2)) = (int_add (int_mul (rem (div x0 x2) x1) x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2))).
Definition term79 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))) x1.
Definition term56 (x0 : int) := ~ ((int_of_num (NUMERAL 0)) = x0).
Definition term51 (x0 : int) (x1 : int) (x2 : int) := div (rem x0 (int_mul x1 x2)).
Definition term44 := rem (int_of_num (NUMERAL 0)).
Definition term97 (x0 : int) (x1 : int) (x2 : int) := @eq int (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term75 (x0 : int) (x1 : int) (x2 : int) := div (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)) x2.
Definition term92 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul (rem (div x1 x2) x0) x2) (rem x1 x2).
Definition term96 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x1 (rem (div x0 x1) x2)).
Definition term93 (x0 : int) (x1 : int) (x2 : int) := int_mul (rem (div x0 x2) x1) x2.
Definition term102 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem (div y0 y1) y2) = (div (rem y0 (int_mul y1 y2)) y1).
Definition term101 (x0 : int) := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem (div x0 y0) y1) = (div (rem x0 (int_mul y0 y1)) y0).
Definition term66 (x0 : int) := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0)).
Definition term16 := forall y0 : int, forall y1 : int, forall y2 : int, (exists y3 : int, (y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2.
Definition term15 (x0 : int) := forall y0 : int, forall y1 : int, (exists y2 : int, (x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> (div x0 y0) = y1.
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> (div x0 x1) = y0.
Definition term2 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> (div x0 y0) = y1.
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2.
Definition term52 (x0 : int) (x1 : int) := div (rem x0 (int_mul (int_of_num (NUMERAL 0)) x1)).
Definition term54 (x0 : int) (x1 : int) := div (rem x0 (int_mul (int_of_num (NUMERAL 0)) x1)) (int_of_num (NUMERAL 0)).
Definition term14 (x0 : int) (x1 : int) := forall y0 : int, (exists y1 : int, (x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> (div x0 x1) = y0.
Definition term6 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x0 = (int_add (int_mul x2 x1) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) -> (div x0 x1) = x2.
Definition term28 (x0 : int) := div x0 (int_of_num (NUMERAL 0)).
Definition term10 (x0 : int) (x1 : int) (x2 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2) -> (div x0 x1) = x2.
Definition term20 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (exists y1 : int, (x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> (div x0 x1) = y0) x2.
Definition term73 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x0) = True.
Definition term95 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul (rem (div x0 x2) x1) x2).
Definition term55 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (rem (div x0 x2) x1) = (div (rem x0 (int_mul x2 x1)) x2).
Definition term38 (x0 : int) := or (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term87 (x0 : int) (x1 : int) := and (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term24 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term17 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2) -> forall y0 : int, forall y1 : int, forall y2 : int, (exists y3 : int, (y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> (div y0 y1) = y2.
Definition term69 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))) x2.
Definition term43 (x0 : int) (x1 : int) := rem (div x0 x1).
Definition term8 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = (int_add (int_mul x3 x2) x0)) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x2)))) -> (div x1 x2) = x3.
Definition term71 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2).
Definition term32 (x0 : int) (x1 : int) := (int_lt x0 x1) \/ (x0 = x1).
Definition term53 (x0 : int) (x1 : int) (x2 : int) := div (rem x0 (int_mul x2 x1)) x2.
Definition term70 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x0 = (int_add (int_mul x2 x1) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) -> (div x0 x1) = x2) x3.
Definition term90 (x0 : int) (x1 : int) (x2 : int) := ((int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)) = (int_add (int_mul (rem (div x1 x2) x0) x2) (rem x1 x2))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x1 x2)) /\ (int_lt (rem x1 x2) (int_abs x2))).
Definition term27 (x0 : int) := (fun y0 : int => (div y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term39 := or (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term82 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term12 (x0 : int) (x1 : int) (x2 : int) := fun y0 : int => (x0 = (int_add (int_mul x1 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2))).
Definition term89 (x0 : int) (x1 : int) (x2 : int) := and ((int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)) = (int_add (int_mul (rem (div x1 x2) x0) x2) (rem x1 x2))).
Definition term21 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term33 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term83 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term47 := int_mul (int_of_num (NUMERAL 0)).
Definition term30 (x0 : int) := forall y0 : int, (int_le x0 y0) = ((int_lt x0 y0) \/ (x0 = y0)).
Definition term49 (x0 : int) (x1 : int) (x2 : int) := rem x0 (int_mul x1 x2).
Definition term41 := (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) \/ True.
Definition term58 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ False.
Definition term50 (x0 : int) (x1 : int) := rem x0 (int_mul (int_of_num (NUMERAL 0)) x1).
Definition term91 (x0 : int) (x1 : int) (x2 : int) := ((int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)) = (int_add (int_mul (rem (div x1 x2) x0) x2) (rem x1 x2))) /\ True.
Definition term45 (x0 : int) (x1 : int) (x2 : int) := rem (div x0 x1) x2.
Definition term76 (x0 : int) (x1 : int) (x2 : int) := (exists y0 : int, ((int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) = (int_add (int_mul (rem (div x0 x1) x2) x1) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) -> (div (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) x1) = (rem (div x0 x1) x2).
Definition term26 (x0 : int) := rem (int_of_num (NUMERAL 0)) x0.
