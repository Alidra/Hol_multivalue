Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (x0 : real) (x1 : real) := forall y0 : real, real_le (real_add y0 (real_neg x0)) (real_add y0 x1).
Definition term40 (x0 : real) (x1 : real) := (real_le x0 x1) -> forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term63 (x0 : real) := real_add (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term37 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) -> real_le (real_add x1 x0) (real_add x1 x2).
Definition term7 (x0 : real) := @eq real (real_add x0 (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) (x1 : real) := real_le (real_neg x0) x1.
Definition term5 := real_of_num (NUMERAL 0).
Definition term45 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0)) x1.
Definition term67 (x0 : real) (x1 : real) := real_add (real_add (real_neg x0) x0) x1.
Definition term28 := forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term9 := fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term43 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term24 (x0 : real) := @eq real (real_add (real_neg x0) x0).
Definition term1 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term65 (x0 : real) := real_le (real_neg x0).
Definition term58 (x0 : real) (x1 : real) := (real_le (real_add x0 (real_neg x0)) (real_add x0 x1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term4 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) (x1 : real) := ((real_le (real_neg x0) x1) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> real_le (real_neg x0) x1).
Definition term47 (x0 : real) (x1 : real) := (real_le (real_neg x0) x1) -> forall y0 : real, real_le (real_add y0 (real_neg x0)) (real_add y0 x1).
Definition term79 := forall y0 : real, forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term42 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term33 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term31 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term15 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term68 (x0 : real) := real_add (real_add (real_neg x0) x0).
Definition term62 (x0 : real) (x1 : real) := real_le (real_add (real_neg x0) (real_of_num (NUMERAL 0))) (real_add (real_neg x0) (real_add x0 x1)).
Definition term55 := real_le (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) := (fun y0 : real => (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0))) x0.
Definition term13 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term22 (x0 : real) := real_add (real_neg x0) x0.
Definition term17 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term57 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term54 (x0 : real) := real_le (real_add x0 (real_neg x0)).
Definition term51 (x0 : real) (x1 : real) := forall y0 : real, real_le (real_add y0 (real_of_num (NUMERAL 0))) (real_add y0 (real_add x0 x1)).
Definition term53 (x0 : real) (x1 : real) := real_le (real_add x0 (real_neg x0)) (real_add x0 x1).
Definition term10 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term39 (x0 : real) (x1 : real) := forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term26 := fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) (x1 : real) := imp (real_le (real_add (real_neg x0) (real_of_num (NUMERAL 0))) (real_add (real_neg x0) (real_add x0 x1))).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2.
Definition term44 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1)) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term27 := fun y0 : real => (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_add x0 x1).
Definition term21 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term74 (x0 : real) (x1 : real) := (forall y0 : real, real_le (real_add y0 (real_of_num (NUMERAL 0))) (real_add y0 (real_add x0 x1))) -> real_le (real_neg x0) x1.
Definition term25 (x0 : real) := @eq real (real_add x0 (real_neg x0)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 x0) (real_add x1 x2).
Definition term23 (x0 : real) := real_add x0 (real_neg x0).
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1)) x1.
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1.
Definition term50 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> forall y0 : real, real_le (real_add y0 (real_of_num (NUMERAL 0))) (real_add y0 (real_add x0 x1)).
Definition term73 (x0 : real) (x1 : real) := (real_le (real_neg x0) x1) -> real_le (real_neg x0) x1.
Definition term49 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term64 (x0 : real) := real_le (real_add (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term35 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0).
Definition term71 (x0 : real) (x1 : real) := imp (real_le (real_neg x0) x1).
Definition term19 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term56 (x0 : real) (x1 : real) := imp (real_le (real_add x0 (real_neg x0)) (real_add x0 x1)).
Definition term6 (x0 : real) := @eq real (real_add (real_of_num (NUMERAL 0)) x0).
Definition term61 (x0 : real) (x1 : real) := (fun y0 : real => real_le (real_add y0 (real_of_num (NUMERAL 0))) (real_add y0 (real_add x1 x0))) (real_neg x1).
Definition term72 (x0 : real) (x1 : real) := (real_le (real_add (real_neg x0) (real_of_num (NUMERAL 0))) (real_add (real_neg x0) (real_add x0 x1))) -> real_le (real_neg x0) x1.
Definition term11 := forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0)) x2.
Definition term3 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term41 (x0 : real) := forall y0 : real, (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0).
Definition term60 (x0 : real) (x1 : real) := (forall y0 : real, real_le (real_add y0 (real_neg x0)) (real_add y0 x1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term29 := forall y0 : real, (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) (x1 : real) := (real_le (real_neg x0) x1) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term59 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term78 (x0 : real) := forall y0 : real, (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term52 (x0 : real) (x1 : real) := (fun y0 : real => real_le (real_add y0 (real_neg x1)) (real_add y0 x0)) x1.
Definition term12 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term20 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term75 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> real_le (real_neg x0) x1.
Definition term69 := real_add (real_of_num (NUMERAL 0)).
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0.
Definition term8 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
