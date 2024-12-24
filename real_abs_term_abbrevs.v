Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : real => @COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0).
Definition term1 (x0 : real) := (fun y0 : real => @COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)) x0.
Definition term4 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term2 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term3 := forall y0 : real, (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0)).
