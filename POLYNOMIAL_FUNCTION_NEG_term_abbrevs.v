Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term43 (x0 : real -> real) (x1 : real) := real_neg (real_neg (x0 x1)).
Definition term51 (x0 : real -> real) (x1 : real) := real_neg (real_mul (real_of_num (NUMERAL (BIT1 0))) (x0 x1)).
Definition term1 (x0 : real) := real_neg (real_neg x0).
Definition term44 (x0 : real -> real) := fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) ((fun y1 : real => real_neg (x0 y1)) y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term54 (x0 : real -> real) := imp (polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y0))).
Definition term46 (x0 : real -> real) := imp (polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) ((fun y1 : real => real_neg (x0 y1)) y0))).
Definition term30 (x0 : real -> real) := polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y0)).
Definition term21 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) -> forall y1 : real, polynomial_function (fun y2 : real => real_mul y1 (y0 y2))) x0.
Definition term40 (x0 : real -> real) := fun y0 : real => (fun y1 : real => real_neg (x0 y1)) y0.
Definition term53 (x0 : real -> real) := fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y0).
Definition term38 (x0 : real -> real) (x1 : real) := (fun y0 : real => (fun y1 : real => real_neg (x0 y1)) y0) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term52 (x0 : real -> real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (x0 x1).
Definition term50 (x0 : real -> real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1).
Definition term32 (x0 : real -> real) (x1 : real) := real_neg (real_mul (real_of_num (NUMERAL (BIT1 0))) ((fun y0 : real => real_neg (x0 y0)) x1)).
Definition term28 (x0 : real -> real) := polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) ((fun y1 : real => real_neg (x0 y1)) y0)).
Definition term22 (x0 : real -> real) := polynomial_function (fun y0 : real => real_neg (x0 y0)).
Definition term14 (x0 : real -> real) (x1 : real) := (fun y0 : real => (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1))) x1.
Definition term60 (x0 : real -> real) := ((polynomial_function (fun y0 : real => real_neg (x0 y0))) -> polynomial_function x0) /\ ((polynomial_function x0) -> polynomial_function (fun y0 : real => real_neg (x0 y0))).
Definition term10 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term12 (x0 : real -> real) := (fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2))) x0.
Definition term55 (x0 : real -> real) := imp (polynomial_function (fun y0 : real => real_neg (x0 y0))).
Definition term42 (x0 : real -> real) (x1 : real) := @eq real ((fun y0 : real => real_neg (x0 y0)) x1).
Definition term45 (x0 : real -> real) := fun y0 : real => x0 y0.
Definition term29 (x0 : real -> real) := (fun y0 : real => polynomial_function (fun y1 : real => real_mul y0 (x0 y1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : real -> real) := (fun y0 : real => polynomial_function (fun y1 : real => real_mul y0 ((fun y2 : real => real_neg (x0 y2)) y1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term49 (x0 : real -> real) := (polynomial_function x0) -> polynomial_function x0.
Definition term34 (x0 : real -> real) (x1 : real) := (fun y0 : real => real_neg (x0 y0)) x1.
Definition term18 (x0 : real -> real) := (polynomial_function x0) -> forall y0 : real, polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term19 := forall y0 : real -> real, (polynomial_function y0) -> forall y1 : real, polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term5 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term0 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term37 (x0 : real -> real) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term13 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term9 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term27 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term41 (x0 : real -> real) (x1 : real) := @eq real ((fun y0 : real => (fun y1 : real => real_neg (x0 y1)) y0) x1).
Definition term7 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term48 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) ((fun y1 : real => real_neg (x0 y1)) y0))) -> polynomial_function x0.
Definition term57 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_neg (x0 y0))) -> polynomial_function (fun y0 : real => real_neg (x0 y0)).
Definition term11 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term59 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_neg (x0 y0))) -> polynomial_function x0.
Definition term33 := real_of_num (NUMERAL (BIT1 0)).
Definition term25 (x0 : real -> real) := forall y0 : real, polynomial_function (fun y1 : real => real_mul y0 ((fun y2 : real => real_neg (x0 y2)) y1)).
Definition term17 (x0 : real -> real) := forall y0 : real, polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term15 (x0 : real) (x1 : real -> real) := (polynomial_function x1) -> polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
Definition term24 (x0 : real -> real) := fun y0 : real => real_neg (x0 y0).
Definition term31 (x0 : real -> real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) ((fun y0 : real => real_neg (x0 y0)) x1).
Definition term20 := (forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2))) -> forall y0 : real -> real, (polynomial_function y0) -> forall y1 : real, polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term23 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_neg (x0 y0))) -> forall y0 : real, polynomial_function (fun y1 : real => real_mul y0 ((fun y2 : real => real_neg (x0 y2)) y1)).
Definition term61 := forall y0 : real -> real, (polynomial_function (fun y1 : real => real_neg (y0 y1))) = (polynomial_function y0).
Definition term47 (x0 : real -> real) := imp (polynomial_function x0).
Definition term56 (x0 : real -> real) := (polynomial_function (fun y0 : real => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y0))) -> polynomial_function (fun y0 : real => real_neg (x0 y0)).
Definition term58 (x0 : real -> real) := (polynomial_function x0) -> polynomial_function (fun y0 : real => real_neg (x0 y0)).
Definition term39 (x0 : real -> real) (x1 : real) := real_neg (x0 x1).
Definition term35 (x0 : real -> real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) ((fun y0 : real => real_neg (x0 y0)) x1).
Definition term16 (x0 : real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
