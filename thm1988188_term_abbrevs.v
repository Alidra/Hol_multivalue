Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (~ (x0 = y0)) = (exists y1 : real, (real_mul (real_sub x0 y0) y1) = (real_of_num (NUMERAL (BIT1 0))))) x1.
Definition term1 (x0 : real) := forall y0 : real, (~ (x0 = y0)) = (exists y1 : real, (real_mul (real_sub x0 y0) y1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (y0 = y1)) = (exists y2 : real, (real_mul (real_sub y0 y1) y2) = (real_of_num (NUMERAL (BIT1 0))))) x0.
