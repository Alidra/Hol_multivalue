Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : real) := real_lt (real_abs x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 := fun y0 : real => True.
Definition term9 := forall y0 : real, True.
Definition term11 (x0 : Prop) := forall y0 : real, x0.
Definition term6 := fun y0 : real => (real_lt (real_abs y0) (real_of_num (NUMERAL (BIT1 0)))) -> (real_div (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))))) = y0.
Definition term4 (x0 : real) := (real_lt (real_abs x0) (real_of_num (NUMERAL (BIT1 0)))) -> (real_div (real_div x0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div x0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs x0)))))) = x0.
Definition term0 (x0 : real) := (fun y0 : real => ((real_div (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))))) = y0) = (real_lt (real_abs y0) (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term5 (x0 : real) := (real_lt (real_abs x0) (real_of_num (NUMERAL (BIT1 0)))) -> real_lt (real_abs x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 := forall y0 : real, (real_lt (real_abs y0) (real_of_num (NUMERAL (BIT1 0)))) -> (real_div (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div y0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs y0)))))) = y0.
Definition term3 (x0 : real) := imp (real_lt (real_abs x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1 (x0 : real) := real_div (real_div x0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div x0 (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs x0))))).
