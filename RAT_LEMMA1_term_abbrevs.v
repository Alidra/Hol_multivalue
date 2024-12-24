Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) (x1 : real) (x2 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2).
Definition term61 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)).
Definition term32 := fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term82 (x0 : real) (x1 : real) := real_mul (real_mul (real_mul x0 x1) (real_inv x1)).
Definition term0 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term69 (x0 : real) := @eq real (real_inv x0).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) (real_mul (real_inv x1) (real_inv x2)).
Definition term81 := real_of_num (NUMERAL 0).
Definition term80 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_add x0 x1) x2.
Definition term62 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul (real_mul x0 x3) (real_mul (real_inv x2) (real_inv x3))) (real_mul (real_mul x1 x2) (real_mul (real_inv x2) (real_inv x3))).
Definition term63 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term68 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x0) x1) (real_inv x1).
Definition term2 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term78 (x0 : real) (x1 : real) := ((real_inv x0) = (real_of_num (NUMERAL 0))) \/ ((real_of_num (NUMERAL (BIT1 0))) = (real_mul x1 (real_inv x1))).
Definition term52 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term44 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_add x0 y0) y1) = (real_add (real_mul x0 y1) (real_mul y0 y1)).
Definition term27 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term26 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term23 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)).
Definition term57 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_div x0 x1) (real_div x2 x3).
Definition term1 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term77 (x0 : real) (x1 : real) := real_mul x0 (real_mul x1 (real_inv x1)).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term59 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add (real_div x0 x1) (real_div x2 x3)).
Definition term3 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term19 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term11 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0)).
Definition term17 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term71 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul (real_mul x0 x1) (real_inv x1)) (real_inv x2).
Definition term67 (x0 : real) (x1 : real) := real_mul x1 (real_mul (real_inv x0) (real_inv x1)).
Definition term21 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term18 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term4 (x0 : real) := real_mul x0 (real_inv x0).
Definition term83 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_mul x0 x2) (real_mul (real_inv x1) (real_inv x2))).
Definition term73 (x0 : real) := @eq real (real_mul (real_inv x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0))) x2.
Definition term20 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term72 (x0 : real) := real_mul (real_inv x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term50 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term6 (x0 : real) := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term66 (x0 : real) (x1 : real) := @eq real (real_mul x0 (real_inv x1)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3))).
Definition term36 (x0 : real) := (fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term7 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) -> forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term58 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3)).
Definition term74 (x0 : real) := @eq real (real_mul x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term51 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x2) (real_mul (real_inv x1) (real_inv x2)).
Definition term45 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_add x0 y0) y1) = (real_add (real_mul x0 y1) (real_mul y0 y1))) x1.
Definition term38 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1))) x1.
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1))) x1.
Definition term25 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term24 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term34 := forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term30 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0))) x2.
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term79 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ ((real_of_num (NUMERAL (BIT1 0))) = (real_mul x1 (real_inv x1))).
Definition term15 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term75 (x0 : real) (x1 : real) := real_mul (real_mul x0 x1) (real_inv x1).
Definition term55 (x0 : real) (x1 : real) := real_add (real_div x0 x1).
Definition term76 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_mul x1 (real_inv x1)).
Definition term84 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x3 = (real_of_num (NUMERAL 0))))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term31 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term54 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x2 (real_mul (real_inv x1) (real_inv x2))).
Definition term16 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term53 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term46 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_add x0 x1) y0) = (real_add (real_mul x0 y0) (real_mul x1 y0)).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul x0 (real_mul x1 x2)).
Definition term40 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term47 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_add x0 x1) y0) = (real_add (real_mul x0 y0) (real_mul x1 y0))) x2.
Definition term56 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_inv x1)).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x0 x2) (real_mul x1 x2).
Definition term43 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_add y0 y1) y2) = (real_add (real_mul y0 y2) (real_mul y1 y2))) x0.
Definition term37 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2))) x0.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y1) = (real_mul y0 y2)) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = y2))) x0.
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ((real_mul (real_mul x1 x0) x2) = (real_mul x1 (real_mul x0 x2))) /\ ((real_mul x1 (real_mul x0 x2)) = (real_mul x0 (real_mul x1 x2))).
Definition term35 := forall y0 : real, y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term33 := fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
