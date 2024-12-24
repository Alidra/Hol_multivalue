Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : int => @COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1))))) x0.
Definition term0 := fun y0 : real => fun y1 : int => @COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1)))).
Definition term6 := forall y0 : real, forall y1 : int, (real_zpow y0 y1) = (@COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1))))).
Definition term2 (x0 : real) := fun y0 : int => @COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0)))).
Definition term4 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term3 (x0 : real) (x1 : int) := (fun y0 : int => @COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0))))) x1.
Definition term8 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0)))))) x1.
Definition term5 (x0 : real) := forall y0 : int, (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0))))).
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 y1) = (@COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1)))))) x0.
