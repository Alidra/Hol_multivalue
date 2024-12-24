Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : real) (x1 : real) := (real_le x0 x1) -> forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term55 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_le x0 x1.
Definition term18 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) -> real_le (real_add x1 x0) (real_add x1 x2).
Definition term37 (x0 : Prop) := ~ (~ x0).
Definition term4 := real_of_num (NUMERAL 0).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0)) x1.
Definition term48 (x0 : real) (x1 : real) := real_add (real_add (real_neg x0) x0) x1.
Definition term41 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term35 (x0 : real) (x1 : real) (x2 : real) := ~ (real_lt (real_add x1 x0) (real_add x1 x2)).
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term24 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x2) -> real_lt (real_add x1 x0) (real_add x1 x2).
Definition term34 (x0 : real) (x1 : real) (x2 : real) := ~ (real_le (real_add x1 x0) (real_add x1 x2)).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x1) (real_add x0 x2)) -> real_le x1 x2.
Definition term59 := forall y0 : real, forall y1 : real, forall y2 : real, (real_lt y1 y2) -> real_lt (real_add y0 y1) (real_add y0 y2).
Definition term58 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (real_add x0 y0) (real_add x0 y1).
Definition term23 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term14 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term6 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term33 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_add x1 x0) (real_add x1 x2).
Definition term49 (x0 : real) := real_add (real_add (real_neg x0) x0).
Definition term0 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term3 (x0 : real) := real_add (real_neg x0) x0.
Definition term8 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term40 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, real_le (real_add y0 (real_add x1 x0)) (real_add y0 (real_add x1 x2)).
Definition term20 (x0 : real) (x1 : real) := forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2.
Definition term27 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1)) x0.
Definition term56 (x0 : real) (x1 : real) (x2 : real) := (forall y0 : real, real_le (real_add y0 (real_add x0 x1)) (real_add y0 (real_add x0 x2))) -> real_le x1 x2.
Definition term39 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x1 x0) (real_add x1 x2)).
Definition term47 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_add x0 x1).
Definition term2 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term19 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 x0) (real_add x1 x2).
Definition term51 (x0 : real) (x1 : real) := real_le (real_add (real_neg x0) (real_add x0 x1)).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1)) x1.
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1.
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x1 x0) (real_add x1 x2)) -> forall y0 : real, real_le (real_add y0 (real_add x1 x0)) (real_add y0 (real_add x1 x2)).
Definition term28 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add (real_neg x1) (real_add x1 x0)) (real_add (real_neg x1) (real_add x1 x2))).
Definition term57 (x0 : real) (x1 : real) := forall y0 : real, (real_lt x0 y0) -> real_lt (real_add x1 x0) (real_add x1 y0).
Definition term16 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := ~ (~ (real_le (real_add x1 x0) (real_add x1 x2))).
Definition term53 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term30 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0)) x2.
Definition term1 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term22 (x0 : real) := forall y0 : real, (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_neg x0) (real_add x0 x1)) (real_add (real_neg x0) (real_add x0 x2))) -> real_le x1 x2.
Definition term46 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_neg x1) (real_add x1 x0)) (real_add (real_neg x1) (real_add x1 x2)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := imp (~ (real_lt (real_add x1 x0) (real_add x1 x2))).
Definition term32 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_add x0 x1) (real_add x0 x2))) -> ~ (real_lt x1 x2).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term45 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_add y0 (real_add x2 x0)) (real_add y0 (real_add x2 x1))) (real_neg x2).
Definition term50 := real_add (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) x0.
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0.
