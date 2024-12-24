Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : int) (x1 : int) := real_lt (real_abs (real_add (real_of_int x0) (real_of_int x1))).
Definition term15 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term14 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_abs x0) (int_sub (int_abs x1) (int_abs x2)).
Definition term34 (x0 : int) (x1 : int) := int_abs (int_add x0 x1).
Definition term12 (x0 : int) (x1 : int) := real_sub (real_abs (real_of_int x0)) (real_abs (real_of_int x1)).
Definition term11 (x0 : int) := real_sub (real_of_int (int_abs x0)).
Definition term9 (x0 : int) := real_lt (real_of_int (int_abs x0)).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_of_int (int_abs x0)) (real_of_int (int_sub (int_abs x1) (int_abs x2))).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_sub (int_abs x0) (int_abs x1)).
Definition term22 (x0 : int) (x1 : int) (x2 : int) := imp (real_lt (real_abs (real_of_int x0)) (real_sub (real_abs (real_of_int x1)) (real_abs (real_of_int x2)))).
Definition term27 (x0 : int) (x1 : int) := real_abs (real_of_int (int_add x0 x1)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => (real_lt (real_abs y0) (real_sub (real_abs (real_of_int x1)) (real_abs (real_of_int x0)))) -> real_lt (real_abs (real_add (real_of_int x0) y0)) (real_abs (real_of_int x1))) (real_of_int x2).
Definition term36 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_abs y0) (int_sub (int_abs x1) (int_abs x0))) -> int_lt (int_abs (int_add x0 y0)) (int_abs x1).
Definition term31 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_abs (real_add (real_of_int x0) (real_of_int x1))) (real_abs (real_of_int x2)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, (real_lt (real_abs y1) (real_sub (real_abs y0) (real_abs (real_of_int x0)))) -> real_lt (real_abs (real_add (real_of_int x0) y1)) (real_abs y0)) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, (real_lt (real_abs y1) (real_sub (real_abs y0) (real_abs (real_of_int x0)))) -> real_lt (real_abs (real_add (real_of_int x0) y1)) (real_abs y0).
Definition term7 (x0 : int) := real_of_int (int_abs x0).
Definition term25 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term23 (x0 : int) (x1 : int) (x2 : int) := imp (int_lt (int_abs x0) (int_sub (int_abs x1) (int_abs x2))).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, (real_lt (real_abs y0) (real_sub (real_abs (real_of_int x1)) (real_abs (real_of_int x0)))) -> real_lt (real_abs (real_add (real_of_int x0) y0)) (real_abs (real_of_int x1)).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_abs y2) (real_sub (real_abs y1) (real_abs y0))) -> real_lt (real_abs (real_add y0 y2)) (real_abs y1)) (real_of_int x0).
Definition term24 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term19 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term10 (x0 : int) := real_sub (real_abs (real_of_int x0)).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (real_lt (real_abs (real_of_int x1)) (real_sub (real_abs (real_of_int x2)) (real_abs (real_of_int x0)))) -> real_lt (real_abs (real_add (real_of_int x0) (real_of_int x1))) (real_abs (real_of_int x2)).
Definition term17 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_abs (real_of_int x0)) (real_sub (real_abs (real_of_int x1)) (real_abs (real_of_int x2))).
Definition term38 := forall y0 : int, forall y1 : int, forall y2 : int, (int_lt (int_abs y2) (int_sub (int_abs y1) (int_abs y0))) -> int_lt (int_abs (int_add y0 y2)) (int_abs y1).
Definition term37 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_abs y1) (int_sub (int_abs y0) (int_abs x0))) -> int_lt (int_abs (int_add x0 y1)) (int_abs y0).
Definition term33 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_abs (int_add x0 x1)) (int_abs x2).
Definition term28 (x0 : int) (x1 : int) := real_of_int (int_abs (int_add x0 x1)).
Definition term32 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_of_int (int_abs (int_add x0 x1))) (real_of_int (int_abs x2)).
Definition term26 (x0 : int) (x1 : int) := real_abs (real_add (real_of_int x0) (real_of_int x1)).
Definition term13 (x0 : int) (x1 : int) := real_sub (real_of_int (int_abs x0)) (real_of_int (int_abs x1)).
Definition term6 (x0 : int) := real_abs (real_of_int x0).
Definition term35 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_abs x1) (int_sub (int_abs x2) (int_abs x0))) -> int_lt (int_abs (int_add x0 x1)) (int_abs x2).
Definition term8 (x0 : int) := real_lt (real_abs (real_of_int x0)).
Definition term21 (x0 : int) (x1 : int) := int_sub (int_abs x0) (int_abs x1).
Definition term30 (x0 : int) (x1 : int) := real_lt (real_of_int (int_abs (int_add x0 x1))).
