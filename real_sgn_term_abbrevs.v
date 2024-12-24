Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) := (fun y0 : real => (real_sgn y0) = (@COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) x0.
Definition term2 (x0 : real) := @COND real (real_lt (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt x0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term3 := forall y0 : real, (real_sgn y0) = (@COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term0 := fun y0 : real => @COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := (fun y0 : real => @COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) x0.
