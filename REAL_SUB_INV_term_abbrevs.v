Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : real) := forall y0 : real, (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term71 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1)))).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term67 (x0 : real) (x1 : real) := @eq real (real_sub (real_inv x0) (real_inv x1)).
Definition term45 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term64 (x0 : real) (x1 : real) := real_mul x0 (real_inv (real_mul x0 x1)).
Definition term92 := real_of_num (NUMERAL 0).
Definition term91 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term69 (x0 : real) (x1 : real) := imp ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term136 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term118 (x0 : real) := fun y0 : real => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_div (real_inv x0) y0)) (real_inv y0)).
Definition term109 (x0 : real) := fun y0 : real => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_mul (real_inv x0) (real_inv y0))) (real_inv y0)).
Definition term103 (x0 : real) := fun y0 : real => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul (real_mul y0 (real_inv x0)) (real_inv y0)) (real_inv y0)).
Definition term134 := fun y0 : real => True.
Definition term47 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term131 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = True.
Definition term37 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term94 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)).
Definition term53 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_sub x0 x1) x2.
Definition term57 (x0 : real) (x1 : real) := real_div (real_sub x1 x0) (real_mul x0 x1).
Definition term135 := forall y0 : real, True.
Definition term137 (x0 : Prop) := forall y0 : real, x0.
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0)) x1.
Definition term56 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term121 := forall y0 : real, forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_div (real_inv y0) y1)) (real_inv y1)).
Definition term112 := forall y0 : real, forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_mul (real_inv y0) (real_inv y1))) (real_inv y1)).
Definition term106 := forall y0 : real, forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul (real_mul y1 (real_inv y0)) (real_inv y1)) (real_inv y1)).
Definition term79 := forall y0 : real, forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_mul (real_inv y0) (real_inv y1))) (real_mul y0 (real_mul (real_inv y0) (real_inv y1)))).
Definition term78 := forall y0 : real, forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_div (real_sub y1 y0) (real_mul y0 y1)).
Definition term49 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1)).
Definition term30 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term29 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term26 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term25 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term14 := forall y0 : real, forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term13 := forall y0 : real, forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term66 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))).
Definition term36 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term107 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_inv x1).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term54 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 x2) (real_mul x1 x2).
Definition term93 (x0 : real) (x1 : real) := real_mul (real_mul x1 (real_inv x0)) (real_inv x1).
Definition term4 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term129 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_div (real_inv x1) x0)) = (real_inv x1).
Definition term95 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x0)) (real_inv x1).
Definition term80 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term34 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term20 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term61 (x0 : real) (x1 : real) := real_mul x1 (real_mul (real_inv x0) (real_inv x1)).
Definition term120 := fun y0 : real => forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_div (real_inv y0) y1)) (real_inv y1)).
Definition term111 := fun y0 : real => forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_mul (real_inv y0) (real_inv y1))) (real_inv y1)).
Definition term105 := fun y0 : real => forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul (real_mul y1 (real_inv y0)) (real_inv y1)) (real_inv y1)).
Definition term77 := fun y0 : real => forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_sub (real_mul y1 (real_mul (real_inv y0) (real_inv y1))) (real_mul y0 (real_mul (real_inv y0) (real_inv y1)))).
Definition term76 := fun y0 : real => forall y1 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv y0) (real_inv y1)) = (real_div (real_sub y1 y0) (real_mul y0 y1)).
Definition term24 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term11 := fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1)).
Definition term96 (x0 : real) := real_mul (real_mul x0 (real_inv x0)).
Definition term8 (x0 : real) := fun y0 : real => (real_mul x0 (real_inv y0)) = (real_div x0 y0).
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term132 (x0 : real) (x1 : real) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = True) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> True).
Definition term38 (x0 : real) := real_mul x0 (real_inv x0).
Definition term7 (x0 : real) := fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term35 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term125 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = y0) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (x2 -> y0)) x3.
Definition term87 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = y0) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (x2 -> y0)) x3.
Definition term117 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1)).
Definition term108 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_inv x1)).
Definition term102 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)) (real_inv x1)).
Definition term114 (x0 : real) (x1 : real) := real_mul x1 (real_div (real_inv x0) x1).
Definition term23 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term12 := fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1).
Definition term127 (x0 : real) (x1 : real) (x2 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = x2) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> x2).
Definition term89 (x0 : real) (x1 : real) (x2 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = x2) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> x2).
Definition term55 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term43 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_inv y1)) = (real_div y0 y1)) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_div y0 y1)) = y0) x0.
Definition term116 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1).
Definition term100 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)) (real_inv x1))).
Definition term124 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = y0) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (x2 -> y0).
Definition term86 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = y0) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (x2 -> y0).
Definition term81 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term130 (x0 : real) := real_sub (real_inv x0).
Definition term3 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_div x1 x0)) = x1.
Definition term63 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))).
Definition term9 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term122 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = y1) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (y0 -> y1).
Definition term83 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = y1) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (y0 -> y1).
Definition term82 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term50 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))) x1.
Definition term41 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term32 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1))) x1.
Definition term128 (x0 : real) (x1 : real) (x2 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = x2) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> x2).
Definition term90 (x0 : real) (x1 : real) (x2 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = x2) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> x2).
Definition term101 (x0 : real) (x1 : real) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)) (real_inv x1)))) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)) (real_inv x1))).
Definition term70 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_div (real_sub x1 x0) (real_mul x0 x1)).
Definition term97 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term46 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term99 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x1 (real_inv x0)) (real_inv x1)) (real_inv x1).
Definition term65 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_inv x0) (real_inv x1)).
Definition term28 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term27 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term72 (x0 : real) := fun y0 : real => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_div (real_sub y0 x0) (real_mul x0 y0)).
Definition term44 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term126 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = x3) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (x2 -> x3).
Definition term88 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = x2) -> (x2 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = x3) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (x2 -> x3).
Definition term33 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0))) x2.
Definition term1 (x0 : real) := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0.
Definition term39 := real_of_num (NUMERAL (BIT1 0)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term133 (x0 : real) (x1 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> True.
Definition term52 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))) x2.
Definition term84 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term19 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0) x1.
Definition term115 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_div (real_inv x0) x1)).
Definition term6 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term119 (x0 : real) := forall y0 : real, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_div (real_inv x0) y0)) (real_inv y0)).
Definition term110 (x0 : real) := forall y0 : real, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_mul (real_inv x0) (real_inv y0))) (real_inv y0)).
Definition term104 (x0 : real) := forall y0 : real, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul (real_mul y0 (real_inv x0)) (real_inv y0)) (real_inv y0)).
Definition term75 (x0 : real) := forall y0 : real, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_mul (real_inv x0) (real_inv y0))) (real_mul x0 (real_mul (real_inv x0) (real_inv y0)))).
Definition term74 (x0 : real) := forall y0 : real, ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_div (real_sub y0 x0) (real_mul x0 y0)).
Definition term113 (x0 : real) (x1 : real) := real_div (real_inv x0) x1.
Definition term51 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0)).
Definition term62 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_inv (real_mul x0 x1))).
Definition term73 (x0 : real) := fun y0 : real => ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv y0)) = (real_sub (real_mul y0 (real_mul (real_inv x0) (real_inv y0))) (real_mul x0 (real_mul (real_inv x0) (real_inv y0)))).
Definition term68 (x0 : real) (x1 : real) := real_sub (real_inv x0) (real_inv x1).
Definition term60 (x0 : real) (x1 : real) := real_mul x1 (real_inv (real_mul x0 x1)).
Definition term123 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = y1) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_div (real_inv x0) x1)) (real_inv x1))) = (y0 -> y1)) x2.
Definition term85 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> ((real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = y1) -> (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) -> (real_sub (real_inv x0) (real_inv x1)) = (real_sub (real_mul x1 (real_mul (real_inv x0) (real_inv x1))) (real_mul x0 (real_mul (real_inv x0) (real_inv x1))))) = (y0 -> y1)) x2.
Definition term48 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))) x0.
Definition term40 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term31 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2))) x0.
Definition term98 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_inv x0).
Definition term5 (x0 : real) (x1 : real) := real_mul x1 (real_div x0 x1).
Definition term58 (x0 : real) (x1 : real) := real_mul (real_sub x1 x0) (real_inv (real_mul x0 x1)).
Definition term59 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_inv (real_mul x0 x1))) (real_mul x0 (real_inv (real_mul x0 x1))).
