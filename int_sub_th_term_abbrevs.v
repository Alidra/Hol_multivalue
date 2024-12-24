Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 := fun y0 : int => forall y1 : int, (real_of_int (int_sub y0 y1)) = (real_sub (real_of_int y0) (real_of_int y1)).
Definition term6 := fun y0 : int => forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1)).
Definition term22 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term5 (x0 : int) := forall y0 : int, (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0)).
Definition term33 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term27 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term50 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 := fun y0 : int => True.
Definition term23 (x0 : int) := (fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_of_real (real_sub (real_of_int y0) (real_of_int y1)))) x0.
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) x0.
Definition term30 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int (int_neg x1)).
Definition term24 (x0 : int) := forall y0 : int, (int_sub x0 y0) = (int_of_real (real_sub (real_of_int x0) (real_of_int y0))).
Definition term31 (x0 : int) (x1 : int) := real_of_int (int_add x0 (int_neg x1)).
Definition term45 (x0 : int) := int_of_real (real_of_int x0).
Definition term39 (x0 : int) := forall y0 : int, (real_of_int (int_sub x0 y0)) = (real_sub (real_of_int x0) (real_of_int y0)).
Definition term4 (x0 : int) := forall y0 : int, (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term42 := fun y0 : int => forall y1 : int, (real_of_int (int_of_real (real_of_int (int_add y0 (int_neg y1))))) = (real_of_int (int_add y0 (int_neg y1))).
Definition term7 := fun y0 : int => forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1)).
Definition term0 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term2 (x0 : int) := fun y0 : int => (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term36 (x0 : int) (x1 : int) := @eq real (real_of_int (int_of_real (real_of_int (int_add x0 (int_neg x1))))).
Definition term29 (x0 : int) := real_add (real_of_int x0).
Definition term38 (x0 : int) := fun y0 : int => (real_of_int (int_of_real (real_of_int (int_add x0 (int_neg y0))))) = (real_of_int (int_add x0 (int_neg y0))).
Definition term32 (x0 : int) (x1 : int) := int_of_real (real_of_int (int_add x0 (int_neg x1))).
Definition term26 (x0 : int) (x1 : int) := int_of_real (real_sub (real_of_int x0) (real_of_int x1)).
Definition term1 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term40 (x0 : int) := forall y0 : int, (real_of_int (int_of_real (real_of_int (int_add x0 (int_neg y0))))) = (real_of_int (int_add x0 (int_neg y0))).
Definition term51 (x0 : Prop) := forall y0 : int, x0.
Definition term44 := forall y0 : int, forall y1 : int, (real_of_int (int_of_real (real_of_int (int_add y0 (int_neg y1))))) = (real_of_int (int_add y0 (int_neg y1))).
Definition term43 := forall y0 : int, forall y1 : int, (real_of_int (int_sub y0 y1)) = (real_sub (real_of_int y0) (real_of_int y1)).
Definition term9 := forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1)).
Definition term8 := forall y0 : int, forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1)).
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term14 := forall y0 : int, (real_of_int (int_neg y0)) = (real_neg (real_of_int y0)).
Definition term15 := forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0)).
Definition term3 (x0 : int) := fun y0 : int => (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0)).
Definition term34 (x0 : int) (x1 : int) := real_of_int (int_of_real (real_of_int (int_add x0 (int_neg x1)))).
Definition term20 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term28 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_neg (real_of_int x1)).
Definition term37 (x0 : int) := fun y0 : int => (real_of_int (int_sub x0 y0)) = (real_sub (real_of_int x0) (real_of_int y0)).
Definition term11 (x0 : int) := real_neg (real_of_int x0).
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term13 := fun y0 : int => (real_neg (real_of_int y0)) = (real_of_int (int_neg y0)).
Definition term49 := forall y0 : int, True.
Definition term18 (x0 : int) := (fun y0 : int => (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) x0.
Definition term46 (x0 : int) (x1 : int) := int_add x0 (int_neg x1).
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0))) x1.
Definition term10 (x0 : int) := real_of_int (int_neg x0).
Definition term25 (x0 : int) (x1 : int) := (fun y0 : int => (int_sub x0 y0) = (int_of_real (real_sub (real_of_int x0) (real_of_int y0)))) x1.
Definition term12 := fun y0 : int => (real_of_int (int_neg y0)) = (real_neg (real_of_int y0)).
Definition term35 (x0 : int) (x1 : int) := @eq real (real_of_int (int_sub x0 x1)).
Definition term47 (x0 : int) (x1 : int) := @eq real (real_of_int (int_add x0 (int_neg x1))).
