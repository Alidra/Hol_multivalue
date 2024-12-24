Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) := (fun y0 : real => (real_sgn y0) = (@COND real (real_lt (real_of_num (NUMERAL 0)) y0) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) (real_of_int x0).
Definition term1 (x0 : int) := real_sgn (real_of_int x0).
Definition term8 := real_of_int (int_of_num (NUMERAL 0)).
Definition term7 := real_of_num (NUMERAL 0).
Definition term12 (x0 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term15 := int_of_num (NUMERAL 0).
Definition term26 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term24 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term30 := real_neg (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term22 (x0 : int) := @COND real (int_lt (int_of_num (NUMERAL 0)) x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term21 (x0 : int) := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term40 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term35 (x0 : int) := @COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term5 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term43 (x0 : int) := @COND real (int_lt (int_of_num (NUMERAL 0)) x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))) (real_of_int (@COND int (int_lt x0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term37 (x0 : int) := @COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term9 := real_lt (real_of_num (NUMERAL 0)).
Definition term45 (x0 : int) := @COND int (int_lt x0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term14 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term42 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term13 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term27 (x0 : int) := @COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term16 (x0 : int) := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term25 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term29 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term10 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term38 (x0 : int) := @COND real (int_lt x0 (int_of_num (NUMERAL 0))) (real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term2 (x0 : int) := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term3 (x0 : int) := real_of_int (int_sgn x0).
Definition term47 := forall y0 : int, (int_sgn y0) = (@COND int (int_lt (int_of_num (NUMERAL 0)) y0) (int_of_num (NUMERAL (BIT1 0))) (@COND int (int_lt y0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term4 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term11 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term46 (x0 : int) := @COND int (int_lt (int_of_num (NUMERAL 0)) x0) (int_of_num (NUMERAL (BIT1 0))) (@COND int (int_lt x0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term31 (x0 : int) := real_neg (real_of_int x0).
Definition term36 (x0 : int) := @COND real (int_lt x0 (int_of_num (NUMERAL 0))) (real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term33 := real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term17 (x0 : int) := @COND real (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term39 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
Definition term18 := real_of_num (NUMERAL (BIT1 0)).
Definition term23 (x0 : int) := real_lt (real_of_int x0).
Definition term32 (x0 : int) := real_of_int (int_neg x0).
Definition term19 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term28 (x0 : int) := @COND real (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term34 := int_of_num (NUMERAL (BIT1 0)).
Definition term41 (x0 : int) := real_of_int (@COND int (int_lt x0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term20 := NUMERAL (BIT1 0).
Definition term44 (x0 : int) := real_of_int (@COND int (int_lt (int_of_num (NUMERAL 0)) x0) (int_of_num (NUMERAL (BIT1 0))) (@COND int (int_lt x0 (int_of_num (NUMERAL 0))) (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
