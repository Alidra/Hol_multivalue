Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real) := forall y0 : real, (real_max x0 (real_max x0 y0)) = (real_max x0 y0).
Definition term54 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_max (int_max x0 x1) x2).
Definition term58 (x0 : int) (x1 : int) (x2 : int) := ((int_max (int_max x1 x2) x0) = (int_max x1 (int_max x2 x0))) /\ (((int_max x1 (int_max x2 x0)) = (int_max x2 (int_max x1 x0))) /\ (((int_max x1 x1) = x1) /\ ((int_max x1 (int_max x1 x2)) = (int_max x1 x2)))).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ((real_max (real_max x1 x2) x0) = (real_max x1 (real_max x2 x0))) /\ (((real_max x1 (real_max x2 x0)) = (real_max x2 (real_max x1 x0))) /\ (((real_max x1 x1) = x1) /\ ((real_max x1 (real_max x1 x2)) = (real_max x1 x2)))).
Definition term26 (x0 : real) (x1 : real) := forall y0 : real, (real_max x1 (real_max x0 y0)) = (real_max x0 (real_max x1 y0)).
Definition term40 (x0 : int) (x1 : int) (x2 : int) := ((int_max x1 (int_max x2 x0)) = (int_max x2 (int_max x1 x0))) /\ (((int_max x1 x1) = x1) /\ ((int_max x1 (int_max x1 x2)) = (int_max x1 x2))).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := ((real_max x1 (real_max x2 x0)) = (real_max x2 (real_max x1 x0))) /\ (((real_max x1 x1) = x1) /\ ((real_max x1 (real_max x1 x2)) = (real_max x1 x2))).
Definition term3 (x0 : real) (x1 : real) := real_max x0 (real_max x0 x1).
Definition term38 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_of_int (int_max x0 (int_max x1 x2))).
Definition term53 (x0 : int) (x1 : int) (x2 : int) := real_max (real_of_int (int_max x0 x1)) (real_of_int x2).
Definition term66 (x0 : int) (x1 : int) (x2 : int) := ((int_max x1 x2) = (int_max x2 x1)) /\ (((int_max (int_max x1 x2) x0) = (int_max x1 (int_max x2 x0))) /\ (((int_max x1 (int_max x2 x0)) = (int_max x2 (int_max x1 x0))) /\ (((int_max x1 x1) = x1) /\ ((int_max x1 (int_max x1 x2)) = (int_max x1 x2))))).
Definition term57 (x0 : int) (x1 : int) (x2 : int) := int_max (int_max x0 x1) x2.
Definition term59 (x0 : real) := forall y0 : real, (real_max y0 x0) = (real_max x0 y0).
Definition term47 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, (real_max (real_max (real_of_int x0) y0) y1) = (real_max (real_of_int x0) (real_max y0 y1))) (real_of_int x1).
Definition term31 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, (real_max y0 (real_max (real_of_int x0) y1)) = (real_max (real_of_int x0) (real_max y0 y1))) (real_of_int x1).
Definition term60 := forall y0 : real, forall y1 : real, (real_max y1 y0) = (real_max y0 y1).
Definition term46 (x0 : int) := forall y0 : real, forall y1 : real, (real_max (real_max (real_of_int x0) y0) y1) = (real_max (real_of_int x0) (real_max y0 y1)).
Definition term44 := forall y0 : real, forall y1 : real, forall y2 : real, (real_max (real_max y0 y1) y2) = (real_max y0 (real_max y1 y2)).
Definition term43 (x0 : real) := forall y0 : real, forall y1 : real, (real_max (real_max x0 y0) y1) = (real_max x0 (real_max y0 y1)).
Definition term30 (x0 : int) := forall y0 : real, forall y1 : real, (real_max y0 (real_max (real_of_int x0) y1)) = (real_max (real_of_int x0) (real_max y0 y1)).
Definition term28 := forall y0 : real, forall y1 : real, forall y2 : real, (real_max y1 (real_max y0 y2)) = (real_max y0 (real_max y1 y2)).
Definition term27 (x0 : real) := forall y0 : real, forall y1 : real, (real_max y0 (real_max x0 y1)) = (real_max x0 (real_max y0 y1)).
Definition term5 := forall y0 : real, forall y1 : real, (real_max y0 (real_max y0 y1)) = (real_max y0 y1).
Definition term56 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_of_int (int_max (int_max x0 x1) x2)).
Definition term42 (x0 : real) (x1 : real) := forall y0 : real, (real_max (real_max x0 x1) y0) = (real_max x0 (real_max x1 y0)).
Definition term51 (x0 : int) (x1 : int) := real_max (real_max (real_of_int x0) (real_of_int x1)).
Definition term32 (x0 : int) (x1 : int) := forall y0 : real, (real_max (real_of_int x1) (real_max (real_of_int x0) y0)) = (real_max (real_of_int x0) (real_max (real_of_int x1) y0)).
Definition term64 (x0 : int) (x1 : int) := @eq real (real_max (real_of_int x0) (real_of_int x1)).
Definition term65 (x0 : int) (x1 : int) := @eq real (real_of_int (int_max x0 x1)).
Definition term61 (x0 : int) := (fun y0 : real => forall y1 : real, (real_max y1 y0) = (real_max y0 y1)) (real_of_int x0).
Definition term45 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_max (real_max y0 y1) y2) = (real_max y0 (real_max y1 y2))) (real_of_int x0).
Definition term29 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_max y1 (real_max y0 y2)) = (real_max y0 (real_max y1 y2))) (real_of_int x0).
Definition term6 (x0 : int) := (fun y0 : real => forall y1 : real, (real_max y0 (real_max y0 y1)) = (real_max y0 y1)) (real_of_int x0).
Definition term62 (x0 : int) := forall y0 : real, (real_max y0 (real_of_int x0)) = (real_max (real_of_int x0) y0).
Definition term7 (x0 : int) := forall y0 : real, (real_max (real_of_int x0) (real_max (real_of_int x0) y0)) = (real_max (real_of_int x0) y0).
Definition term37 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_max (real_of_int x0) (real_max (real_of_int x1) (real_of_int x2))).
Definition term15 (x0 : int) (x1 : int) := @eq real (real_max (real_of_int x0) (real_max (real_of_int x0) (real_of_int x1))).
Definition term55 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_max (real_max (real_of_int x0) (real_of_int x1)) (real_of_int x2)).
Definition term24 (x0 : int) (x1 : int) := ((int_max x0 x0) = x0) /\ ((int_max x0 (int_max x0 x1)) = (int_max x0 x1)).
Definition term13 (x0 : int) (x1 : int) := real_max (real_of_int x0) (real_of_int (int_max x0 x1)).
Definition term18 := forall y0 : real, (real_max y0 y0) = y0.
Definition term36 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_max x0 (int_max x1 x2)).
Definition term49 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => (real_max (real_max (real_of_int x0) (real_of_int x1)) y0) = (real_max (real_of_int x0) (real_max (real_of_int x1) y0))) (real_of_int x2).
Definition term21 (x0 : int) := real_of_int (int_max x0 x0).
Definition term17 (x0 : int) (x1 : int) := int_max x0 (int_max x0 x1).
Definition term35 (x0 : int) (x1 : int) (x2 : int) := real_max (real_of_int x0) (real_of_int (int_max x1 x2)).
Definition term34 (x0 : int) (x1 : int) (x2 : int) := real_max (real_of_int x0) (real_max (real_of_int x1) (real_of_int x2)).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := real_max (real_max x0 x1) x2.
Definition term16 (x0 : int) (x1 : int) := @eq real (real_of_int (int_max x0 (int_max x0 x1))).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := real_max x0 (real_max x1 x2).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_max x0 x1).
Definition term33 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => (real_max (real_of_int x1) (real_max (real_of_int x0) y0)) = (real_max (real_of_int x0) (real_max (real_of_int x1) y0))) (real_of_int x2).
Definition term22 (x0 : int) := @eq real (real_max (real_of_int x0) (real_of_int x0)).
Definition term19 (x0 : int) := (fun y0 : real => (real_max y0 y0) = y0) (real_of_int x0).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := int_max x0 (int_max x1 x2).
Definition term9 (x0 : int) (x1 : int) := real_max (real_of_int x0) (real_max (real_of_int x0) (real_of_int x1)).
Definition term52 (x0 : int) (x1 : int) := real_max (real_of_int (int_max x0 x1)).
Definition term48 (x0 : int) (x1 : int) := forall y0 : real, (real_max (real_max (real_of_int x0) (real_of_int x1)) y0) = (real_max (real_of_int x0) (real_max (real_of_int x1) y0)).
Definition term14 (x0 : int) (x1 : int) := real_of_int (int_max x0 (int_max x0 x1)).
Definition term12 (x0 : int) := real_max (real_of_int x0).
Definition term23 (x0 : int) := @eq real (real_of_int (int_max x0 x0)).
Definition term50 (x0 : int) (x1 : int) (x2 : int) := real_max (real_max (real_of_int x0) (real_of_int x1)) (real_of_int x2).
Definition term10 (x0 : int) (x1 : int) := real_max (real_of_int x0) (real_of_int x1).
Definition term20 (x0 : int) := real_max (real_of_int x0) (real_of_int x0).
Definition term2 (x0 : real) (x1 : real) := ((real_max x0 x0) = x0) /\ ((real_max x0 (real_max x0 x1)) = (real_max x0 x1)).
Definition term63 (x0 : int) (x1 : int) := (fun y0 : real => (real_max y0 (real_of_int x0)) = (real_max (real_of_int x0) y0)) (real_of_int x1).
Definition term8 (x0 : int) (x1 : int) := (fun y0 : real => (real_max (real_of_int x0) (real_max (real_of_int x0) y0)) = (real_max (real_of_int x0) y0)) (real_of_int x1).
