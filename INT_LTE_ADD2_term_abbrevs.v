Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : int) (x1 : int) := real_lt (real_add (real_of_int x0) (real_of_int x1)).
Definition term20 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := real_lt (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x2) (real_of_int x3)).
Definition term24 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((int_lt x0 x2) /\ (int_le x1 y0)) -> int_lt (int_add x0 x1) (int_add x2 y0).
Definition term15 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((int_lt x0 x1) /\ (int_le x2 x3)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_int x0) y0) /\ (real_le y1 y2)) -> real_lt (real_add (real_of_int x0) y1) (real_add y0 y2)) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, forall y1 : real, ((real_lt (real_of_int x0) (real_of_int x1)) /\ (real_le y0 y1)) -> real_lt (real_add (real_of_int x0) y0) (real_add (real_of_int x1) y1).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_int x0) y0) /\ (real_le y1 y2)) -> real_lt (real_add (real_of_int x0) y1) (real_add y0 y2).
Definition term6 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : real => ((real_lt (real_of_int x0) (real_of_int x2)) /\ (real_le (real_of_int x1) y0)) -> real_lt (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x2) y0)) (real_of_int x3).
Definition term22 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := int_lt (int_add x0 x1) (int_add x2 x3).
Definition term17 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := forall y0 : real, ((real_lt (real_of_int x0) (real_of_int x2)) /\ (real_le (real_of_int x1) y0)) -> real_lt (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x2) y0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3)) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) := and (int_lt x0 x1).
Definition term16 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term8 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term13 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) /\ (int_le x2 x3).
Definition term9 (x0 : int) (x1 : int) := and (real_lt (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_int x0) (real_of_int x1)) /\ (real_le y0 y1)) -> real_lt (real_add (real_of_int x0) y0) (real_add (real_of_int x1) y1)) (real_of_int x2).
Definition term27 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_lt y0 y1) /\ (int_le y2 y3)) -> int_lt (int_add y0 y2) (int_add y1 y3).
Definition term26 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((int_lt x0 y0) /\ (int_le y1 y2)) -> int_lt (int_add x0 y1) (int_add y0 y2).
Definition term25 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((int_lt x0 x1) /\ (int_le y0 y1)) -> int_lt (int_add x0 y0) (int_add x1 y1).
Definition term21 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := real_lt (real_of_int (int_add x0 x1)) (real_of_int (int_add x2 x3)).
Definition term23 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_lt x0 x2) /\ (int_le x1 x3)) -> int_lt (int_add x0 x1) (int_add x2 x3).
Definition term11 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term12 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (real_lt (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x2) (real_of_int x3)).
Definition term14 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((real_lt (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x2) (real_of_int x3))).
Definition term19 (x0 : int) (x1 : int) := real_lt (real_of_int (int_add x0 x1)).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((real_lt (real_of_int x0) (real_of_int x2)) /\ (real_le (real_of_int x1) (real_of_int x3))) -> real_lt (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x2) (real_of_int x3)).
