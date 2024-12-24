Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : real) := forall y0 : real, (real_le (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))) = (real_le x0 y0).
Definition term10 (x0 : real) := forall y0 : real, (real_lt (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))) = (real_lt x0 y0).
Definition term24 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : real) (x1 : real) := @eq Prop (real_le (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div x1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x1)))).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))) = (real_lt x0 y0)) x1.
Definition term14 (x0 : real) (x1 : real) := (fun y0 : real => (real_le y0 x0) = (~ (real_lt x0 y0))) x1.
Definition term21 := fun y0 : real => True.
Definition term23 := forall y0 : real, True.
Definition term25 (x0 : Prop) := forall y0 : real, x0.
Definition term19 (x0 : real) (x1 : real) := @eq Prop (~ (real_lt x0 x1)).
Definition term27 := forall y0 : real, forall y1 : real, (real_le (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_div y1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y1)))) = (real_le y0 y1).
Definition term8 := forall y0 : real, forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1)).
Definition term7 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term1 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term3 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term0 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term26 := fun y0 : real => forall y1 : real, (real_le (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_div y1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y1)))) = (real_le y0 y1).
Definition term5 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1))) x0.
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_div y1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y1)))) = (real_lt y0 y1)) x0.
Definition term20 (x0 : real) := fun y0 : real => (real_le (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div y0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))) = (real_le x0 y0).
Definition term17 (x0 : real) := real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0)).
Definition term4 (x0 : real) := forall y0 : real, (real_le y0 x0) = (~ (real_lt x0 y0)).
Definition term16 (x0 : real) (x1 : real) := ~ (real_lt (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div x1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x1)))).
Definition term12 (x0 : real) (x1 : real) := real_lt (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div x1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x1))).
Definition term2 (x0 : real) := fun y0 : real => (real_le y0 x0) = (~ (real_lt x0 y0)).
Definition term15 (x0 : real) (x1 : real) := real_le (real_div x0 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_div x1 (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x1))).
Definition term6 := fun y0 : real => forall y1 : real, (real_le y1 y0) = (~ (real_lt y0 y1)).
