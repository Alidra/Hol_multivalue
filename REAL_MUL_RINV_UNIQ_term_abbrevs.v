Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term15 := forall y0 : real, forall y1 : real, ((real_mul y1 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term14 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term5 (x0 : real) (x1 : real) := imp ((real_mul x0 x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 (x0 : real) := fun y0 : real => ((real_mul y0 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term8 (x0 : real) := fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term13 := fun y0 : real => forall y1 : real, ((real_mul y1 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term12 := fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term11 (x0 : real) := forall y0 : real, ((real_mul y0 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term10 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term7 (x0 : real) (x1 : real) := ((real_mul x1 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term6 (x0 : real) (x1 : real) := ((real_mul x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term17 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = x0.
Definition term3 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term4 := real_of_num (NUMERAL (BIT1 0)).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = x0) x1.
