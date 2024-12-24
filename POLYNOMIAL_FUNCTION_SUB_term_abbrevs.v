Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term51 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 (x0 : real -> real) (x1 : real -> real) (x2 : real) := real_add (x0 x2) (real_neg (x1 x2)).
Definition term39 (x0 : real -> real) (x1 : real -> real) := imp ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_neg (x1 y0)))).
Definition term7 (x0 : real -> real) := polynomial_function (fun y0 : real => real_neg (x0 y0)).
Definition term44 (x0 : real -> real) (x1 : real -> real) := (((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = True) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = (((polynomial_function x0) /\ (polynomial_function x1)) -> True).
Definition term40 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_neg (x1 y0)))) -> (polynomial_function (fun y0 : real => real_add (x0 y0) (real_neg (x1 y0)))) = True.
Definition term29 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_neg (x1 y0)))) -> (polynomial_function (fun y0 : real => real_add (x0 y0) ((fun y1 : real => real_neg (x1 y1)) y0))) = True.
Definition term45 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0)).
Definition term3 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_add (x0 y0) (x1 y0)).
Definition term27 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_add (x0 y0) (real_neg (x1 y0))).
Definition term43 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = True.
Definition term28 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_add (x0 y0) (x1 y0))) = True.
Definition term4 (x0 : real -> real) (x1 : real -> real) := (polynomial_function x0) /\ (polynomial_function x1).
Definition term0 (x0 : real -> real) := (fun y0 : real -> real => forall y1 : real -> real, ((polynomial_function y0) /\ (polynomial_function y1)) -> polynomial_function (fun y2 : real => real_add (y0 y2) (y1 y2))) x0.
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term49 (x0 : real -> real) := forall y0 : real -> real, ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (y0 y1)).
Definition term1 (x0 : real -> real) := forall y0 : real -> real, ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_add (x0 y1) (y0 y1)).
Definition term31 (x0 : real -> real) (x1 : real) := (fun y0 : real => real_neg (x0 y0)) x1.
Definition term53 := fun y0 : real -> real => forall y1 : real -> real, ((polynomial_function y0) /\ (polynomial_function y1)) -> polynomial_function (fun y2 : real => real_sub (y0 y2) (y1 y2)).
Definition term48 := fun y0 : real -> real => True.
Definition term6 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function (fun y1 : real => real_neg (y0 y1))) = (polynomial_function y0)) x0.
Definition term38 (x0 : real -> real) (x1 : real -> real) := @eq Prop (polynomial_function (fun y0 : real => real_add (x0 y0) (real_neg (x1 y0)))).
Definition term37 (x0 : real -> real) (x1 : real -> real) := @eq Prop (polynomial_function (fun y0 : real => real_add (x0 y0) ((fun y1 : real => real_neg (x1 y1)) y0))).
Definition term50 := forall y0 : real -> real, True.
Definition term35 (x0 : real -> real) (x1 : real -> real) := fun y0 : real => real_add (x0 y0) ((fun y1 : real => real_neg (x1 y1)) y0).
Definition term16 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0)).
Definition term42 (x0 : real -> real) (x1 : real -> real) := (polynomial_function x0) /\ (polynomial_function (fun y0 : real => real_neg (x1 y0))).
Definition term2 (x0 : real -> real) (x1 : real -> real) := (fun y0 : real -> real => ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_add (x0 y1) (y0 y1))) x1.
Definition term19 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((polynomial_function x0) /\ (polynomial_function x1)) = x2) -> (x2 -> (polynomial_function (fun y1 : real => real_sub (x0 y1) (x1 y1))) = y0) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (x1 y1))) = (x2 -> y0)) x3.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term18 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) := forall y0 : Prop, (((polynomial_function x0) /\ (polynomial_function x1)) = x2) -> (x2 -> (polynomial_function (fun y1 : real => real_sub (x0 y1) (x1 y1))) = y0) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (x1 y1))) = (x2 -> y0).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term47 (x0 : real -> real) := fun y0 : real -> real => ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (y0 y1)).
Definition term9 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term15 (x0 : real -> real) (x1 : real -> real) := forall y0 : Prop, forall y1 : Prop, (((polynomial_function x0) /\ (polynomial_function x1)) = y0) -> (y0 -> (polynomial_function (fun y2 : real => real_sub (x0 y2) (x1 y2))) = y1) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y2 : real => real_sub (x0 y2) (x1 y2))) = (y0 -> y1).
Definition term14 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term54 := forall y0 : real -> real, forall y1 : real -> real, ((polynomial_function y0) /\ (polynomial_function y1)) -> polynomial_function (fun y2 : real => real_sub (y0 y2) (y1 y2)).
Definition term25 (x0 : real -> real) (x1 : real -> real) := fun y0 : real => real_sub (x0 y0) (x1 y0).
Definition term20 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) (x3 : Prop) := (((polynomial_function x0) /\ (polynomial_function x1)) = x2) -> (x2 -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = x3) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = (x2 -> x3).
Definition term52 (x0 : Prop) := forall y0 : real -> real, x0.
Definition term36 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_add (x0 y0) ((fun y1 : real => real_neg (x1 y1)) y0)).
Definition term34 (x0 : real -> real) (x1 : real -> real) (x2 : real) := real_add (x0 x2) ((fun y0 : real => real_neg (x1 y0)) x2).
Definition term46 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> True.
Definition term30 (x0 : real -> real) := fun y0 : real => real_neg (x0 y0).
Definition term21 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) := (((polynomial_function x0) /\ (polynomial_function x1)) = ((polynomial_function x0) /\ (polynomial_function x1))) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = x2) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = (((polynomial_function x0) /\ (polynomial_function x1)) -> x2).
Definition term26 (x0 : real -> real) (x1 : real -> real) := fun y0 : real => real_add (x0 y0) (real_neg (x1 y0)).
Definition term5 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_add (x0 y0) (x1 y0)).
Definition term33 (x0 : real -> real) (x1 : real) := real_add (x0 x1).
Definition term32 (x0 : real -> real) (x1 : real) := real_neg (x0 x1).
Definition term17 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((polynomial_function x0) /\ (polynomial_function x1)) = y0) -> (y0 -> (polynomial_function (fun y2 : real => real_sub (x0 y2) (x1 y2))) = y1) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y2 : real => real_sub (x0 y2) (x1 y2))) = (y0 -> y1)) x2.
Definition term22 (x0 : real -> real) (x1 : real -> real) (x2 : Prop) := (((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = x2) -> (((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = (((polynomial_function x0) /\ (polynomial_function x1)) -> x2).
Definition term23 (x0 : real -> real) (x1 : real -> real) (x2 : real) := real_sub (x0 x2) (x1 x2).
Definition term41 (x0 : real -> real) := and (polynomial_function x0).
