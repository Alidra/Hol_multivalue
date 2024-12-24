Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) := forall y0 : real, (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term36 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term61 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) := real_mul (real_add (real_mul x0 x1) (real_mul x2 x3)) x4.
Definition term58 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_mul x3 x4)) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ((real_div x0 (real_mul x3 x4)) = (real_div x2 x1)) = ((real_mul x0 x1) = (real_mul x2 (real_mul x3 x4))).
Definition term21 (x0 : real) := fun y0 : real => (real_mul (real_inv x0) (real_inv y0)) = (real_inv (real_mul x0 y0)).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term8 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term19 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term7 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (real_lt (real_of_num (NUMERAL 0)) x2).
Definition term37 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0)) x1.
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_inv x0) (real_inv y0)) = (real_inv (real_mul x0 y0))) x1.
Definition term68 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt (real_of_num (NUMERAL 0)) x3) -> (real_lt (real_of_num (NUMERAL 0)) x5) -> ((real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) x5) = (real_mul x4 (real_mul x1 x3))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term27 := forall y0 : real, forall y1 : real, (real_mul (real_inv y0) (real_inv y1)) = (real_inv (real_mul y0 y1)).
Definition term26 := forall y0 : real, forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1)).
Definition term17 := forall y0 : real, forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term16 := forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term0 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term35 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_div x0 x1) (real_div x2 x3).
Definition term33 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term2 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term40 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)))).
Definition term24 := fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1)).
Definition term14 := fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term55 (x0 : real) (x1 : real) := and (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1)).
Definition term47 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := @eq Prop ((real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5)).
Definition term11 (x0 : real) := fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term45 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (fun y0 : real => y0 = (real_div x0 x1)) (real_mul (real_add (real_mul x2 x5) (real_mul x3 x4)) (real_mul (real_inv x4) (real_inv x5))).
Definition term56 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ True.
Definition term38 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := True -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term10 (x0 : real) := fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term64 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_mul x2 x3)) /\ (real_lt (real_of_num (NUMERAL 0)) x5)) -> (real_div (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul x2 x3)) = (real_div x4 x5).
Definition term59 (x0 : real) (x1 : real) (x2 : real) := real_div x0 (real_mul x1 x2).
Definition term43 (x0 : real) (x1 : real) := fun y0 : real => y0 = (real_div x0 x1).
Definition term15 := fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term52 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_inv y0) (real_inv y1)) = (real_inv (real_mul y0 y1))) x0.
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1)) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term4 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term48 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x1) (real_mul x2 x3)).
Definition term53 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_div (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul x2 x3)).
Definition term5 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term6 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term23 (x0 : real) := forall y0 : real, (real_mul (real_inv x0) (real_inv y0)) = (real_inv (real_mul x0 y0)).
Definition term12 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term34 (x0 : real) (x1 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term18 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term32 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term22 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term44 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (fun y0 : real => y0 = (real_div x0 x1)) (real_add (real_div x2 x3) (real_div x4 x5)).
Definition term51 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 x1) (real_mul x2 x3).
Definition term65 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := ((real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) x5) = (real_mul x4 (real_mul x1 x3))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term42 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := ((real_add (real_div x0 x1) (real_div x2 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) (real_mul (real_inv x1) (real_inv x3)))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term49 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_inv (real_mul x2 x3)).
Definition term20 (x0 : real) := fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term41 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) (real_mul (real_inv x1) (real_inv x3)))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term46 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := @eq Prop ((fun y0 : real => y0 = (real_div x0 x1)) (real_add (real_div x2 x3) (real_div x4 x5))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)))).
Definition term9 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term67 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (real_lt (real_of_num (NUMERAL 0)) x3) -> (real_lt (real_of_num (NUMERAL 0)) x5) -> ((real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) x5) = (real_mul x4 (real_mul x1 x3))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul x0 (real_mul x1 x2)).
Definition term57 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ((real_div x0 x3) = (real_div x2 x1)) = ((real_mul x0 x1) = (real_mul x2 x3)).
Definition term62 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) := @eq real (real_mul (real_add (real_mul x0 x1) (real_mul x2 x3)) x4).
Definition term50 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_div (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul x2 x3).
Definition term66 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : real) (x5 : real) := (real_lt (real_of_num (NUMERAL 0)) x5) -> ((real_mul (real_add (real_mul x0 x3) (real_mul x2 x1)) x5) = (real_mul x4 (real_mul x1 x3))) -> (real_add (real_div x0 x1) (real_div x2 x3)) = (real_div x4 x5).
Definition term25 := fun y0 : real => forall y1 : real, (real_mul (real_inv y0) (real_inv y1)) = (real_inv (real_mul y0 y1)).
