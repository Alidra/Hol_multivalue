Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term54 (x0 : real) (x1 : real) := real_le (real_neg (real_of_num (NUMERAL 0))) (real_neg (real_add x0 x1)).
Definition term1 (x0 : real) := real_neg (real_neg x0).
Definition term37 (x0 : real) (x1 : real) := real_le (real_neg x0) x1.
Definition term8 := real_of_num (NUMERAL 0).
Definition term11 := forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) := fun y0 : real => (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term43 (x0 : real) := (fun y0 : real => y0 = (real_neg (real_neg y0))) x0.
Definition term60 (x0 : real) := real_add (real_neg (real_neg x0)).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_le y0 x0) = (real_le (real_neg x0) (real_neg y0))) x1.
Definition term56 (x0 : real) := @eq real (real_add (real_neg x0) x0).
Definition term63 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term57 := real_neg (real_of_num (NUMERAL 0)).
Definition term16 (x0 : real) := fun y0 : real => (real_le y0 x0) = (real_le (real_neg x0) (real_neg y0)).
Definition term15 (x0 : real) := fun y0 : real => (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0).
Definition term64 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term40 := fun y0 : real => y0 = (real_neg (real_neg y0)).
Definition term67 := forall y0 : real, forall y1 : real, (real_le y0 (real_neg y1)) = (real_le (real_add y0 y1) (real_of_num (NUMERAL 0))).
Definition term31 := forall y0 : real, forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1)).
Definition term30 := forall y0 : real, forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1)).
Definition term22 := forall y0 : real, forall y1 : real, (real_le y1 y0) = (real_le (real_neg y0) (real_neg y1)).
Definition term21 := forall y0 : real, forall y1 : real, (real_le (real_neg y0) (real_neg y1)) = (real_le y1 y0).
Definition term41 := forall y0 : real, (real_neg (real_neg y0)) = y0.
Definition term42 := forall y0 : real, y0 = (real_neg (real_neg y0)).
Definition term51 := real_le (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) := real_le x0 (real_neg x1).
Definition term13 (x0 : real) := (fun y0 : real => (real_of_num (NUMERAL 0)) = (real_add (real_neg y0) y0)) x0.
Definition term14 (x0 : real) (x1 : real) := real_le (real_neg x0) (real_neg x1).
Definition term65 := real_le (real_neg (real_of_num (NUMERAL 0))).
Definition term28 := fun y0 : real => forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1)).
Definition term20 := fun y0 : real => forall y1 : real, (real_le y1 y0) = (real_le (real_neg y0) (real_neg y1)).
Definition term50 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add (real_neg x0) (real_neg x1)).
Definition term7 (x0 : real) := real_add (real_neg x0) x0.
Definition term53 (x0 : real) (x1 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (real_neg (real_add x0 x1))).
Definition term55 := @eq real (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := real_add (real_neg (real_neg x0)) (real_neg x0).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0))) x1.
Definition term47 (x0 : real) (x1 : real) := @eq Prop (real_le x0 (real_neg x1)).
Definition term0 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term27 (x0 : real) := forall y0 : real, (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0)).
Definition term9 := fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term36 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0))) x1.
Definition term19 := fun y0 : real => forall y1 : real, (real_le (real_neg y0) (real_neg y1)) = (real_le y1 y0).
Definition term52 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg (real_add x0 x1)).
Definition term17 (x0 : real) := forall y0 : real, (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0).
Definition term62 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term34 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) x0.
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1))) x0.
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y1 y0) = (real_le (real_neg y0) (real_neg y1))) x0.
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1))) x0.
Definition term66 (x0 : real) := forall y0 : real, (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term26 (x0 : real) := fun y0 : real => (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0)).
Definition term5 (x0 : real) (x1 : real) := real_neg (real_add x0 x1).
Definition term61 (x0 : real) := real_add x0 (real_neg x0).
Definition term10 := fun y0 : real => (real_of_num (NUMERAL 0)) = (real_add (real_neg y0) y0).
Definition term38 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term33 (x0 : real) (x1 : real) := (fun y0 : real => (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0))) x1.
Definition term3 (x0 : real) := forall y0 : real, (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term6 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_neg x1).
Definition term49 (x0 : real) (x1 : real) := real_le (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) := real_neg (real_add (real_neg x0) x0).
Definition term44 (x0 : real) := real_le (real_neg (real_neg x0)).
Definition term35 (x0 : real) := forall y0 : real, (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term18 (x0 : real) := forall y0 : real, (real_le y0 x0) = (real_le (real_neg x0) (real_neg y0)).
Definition term46 (x0 : real) (x1 : real) := real_le (real_neg (real_neg x0)) (real_neg x1).
Definition term12 := forall y0 : real, (real_of_num (NUMERAL 0)) = (real_add (real_neg y0) y0).
Definition term39 := fun y0 : real => (real_neg (real_neg y0)) = y0.
Definition term29 := fun y0 : real => forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1)).
Definition term48 (x0 : real) (x1 : real) := @eq Prop (real_le (real_neg (real_neg x0)) (real_neg x1)).
