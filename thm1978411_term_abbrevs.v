Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 (x0 : real) (x1 : real) := real_add (real_mul x0 x1).
Definition term17 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)).
Definition term47 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term41 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, forall y1 : real, (real_add (real_mul y0 (real_inv x2)) (real_mul y1 (real_inv x3))) = (real_mul (real_add (real_mul y0 x3) (real_mul y1 x2)) (real_mul (real_inv x2) (real_inv x3)))) -> (real_sub (real_mul x0 (real_inv x2)) (real_mul x1 (real_inv x3))) = (real_mul (real_sub (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term59 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 x1) (real_mul (real_neg x2) x3).
Definition term32 (x0 : real) (x1 : real) := imp (forall y0 : real, forall y1 : real, (real_add (real_mul y0 (real_inv x0)) (real_mul y1 (real_inv x1))) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1)))).
Definition term31 (x0 : real) (x1 : real) := imp (forall y0 : real, forall y1 : real, (real_add (real_div y0 x0) (real_div y1 x1)) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1)))).
Definition term2 (x0 : real) := fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term62 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term60 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_sub (real_mul x0 x1) (real_mul x2 x3)).
Definition term61 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x1) (real_mul (real_neg x2) x3)).
Definition term15 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_sub (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)).
Definition term43 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)) x1.
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term40 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, forall y1 : real, (real_add (real_div y0 x2) (real_div y1 x3)) = (real_mul (real_add (real_mul y0 x3) (real_mul y1 x2)) (real_mul (real_inv x2) (real_inv x3)))) -> (real_sub (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_sub (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term30 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, (real_add (real_mul y0 (real_inv x0)) (real_mul y1 (real_inv x1))) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1))).
Definition term19 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, (real_add (real_div y0 x0) (real_div y1 x1)) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1))).
Definition term9 := forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1).
Definition term8 := forall y0 : real, forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)).
Definition term16 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_div x0 x1) (real_div x2 x3).
Definition term34 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_inv x1)).
Definition term53 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 (real_inv x1)) (real_mul (real_neg x2) (real_inv x3)).
Definition term1 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term23 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add (real_div x0 x1) (real_div x2 x3)).
Definition term37 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_sub (real_div x0 x1) (real_div x2 x3)).
Definition term29 (x0 : real) (x1 : real) := fun y0 : real => forall y1 : real, (real_add (real_mul y0 (real_inv x0)) (real_mul y1 (real_inv x1))) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1))).
Definition term28 (x0 : real) (x1 : real) := fun y0 : real => forall y1 : real, (real_add (real_div y0 x0) (real_div y1 x1)) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1))).
Definition term27 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, (real_add (real_mul x0 (real_inv x1)) (real_mul y0 (real_inv x2))) = (real_mul (real_add (real_mul x0 x2) (real_mul y0 x1)) (real_mul (real_inv x1) (real_inv x2))).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, (real_add (real_div x0 x1) (real_div y0 x2)) = (real_mul (real_add (real_mul x0 x2) (real_mul y0 x1)) (real_mul (real_inv x1) (real_inv x2))).
Definition term7 := fun y0 : real => forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1).
Definition term57 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 x1) (real_neg (real_mul x2 x3)).
Definition term55 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_mul (real_add (real_mul x0 x3) (real_mul (real_neg x1) x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term44 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term42 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)) x0.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term24 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3))).
Definition term0 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term14 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term49 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => (real_add (real_mul x0 (real_inv x1)) (real_mul y0 (real_inv x2))) = (real_mul (real_add (real_mul x0 x2) (real_mul y0 x1)) (real_mul (real_inv x1) (real_inv x2)))) x3.
Definition term22 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3)).
Definition term45 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term11 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term4 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term50 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 (real_inv x1)) (real_neg (real_mul x2 (real_inv x3))).
Definition term46 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term51 (x0 : real) (x1 : real) := real_neg (real_mul x0 (real_inv x1)).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, (real_add (real_mul y0 (real_inv x0)) (real_mul y1 (real_inv x1))) = (real_mul (real_add (real_mul y0 x1) (real_mul y1 x0)) (real_mul (real_inv x0) (real_inv x1)))) x2.
Definition term25 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (real_add (real_div x0 x1) (real_div y0 x2)) = (real_mul (real_add (real_mul x0 x2) (real_mul y0 x1)) (real_mul (real_inv x1) (real_inv x2))).
Definition term56 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_mul x0 x1) (real_mul x2 x3).
Definition term20 (x0 : real) (x1 : real) := real_add (real_div x0 x1).
Definition term3 (x0 : real) := fun y0 : real => (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0).
Definition term35 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_div x0 x1) (real_div x2 x3).
Definition term33 (x0 : real) (x1 : real) := real_sub (real_div x0 x1).
Definition term13 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term26 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (real_add (real_mul x0 (real_inv x1)) (real_mul y0 (real_inv x2))) = (real_mul (real_add (real_mul x0 x2) (real_mul y0 x1)) (real_mul (real_inv x1) (real_inv x2))).
Definition term21 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_inv x1)).
Definition term5 (x0 : real) := forall y0 : real, (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0).
Definition term38 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_sub (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3))).
Definition term36 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3)).
Definition term6 := fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1)).
Definition term52 (x0 : real) (x1 : real) := real_mul (real_neg x0) (real_inv x1).
Definition term54 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul (real_neg x1) x2)) (real_mul (real_inv x2) (real_inv x3)).
