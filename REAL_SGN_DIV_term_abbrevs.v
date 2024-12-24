Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0)))) x1.
Definition term90 (x0 : real) (x1 : real) := real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1)))).
Definition term105 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_abs x1) (real_inv x1)).
Definition term14 (x0 : real) (x1 : real) := real_abs (real_div x0 x1).
Definition term41 (x0 : real) (x1 : real) := real_inv (real_mul (real_abs x0) (real_inv (real_abs x1))).
Definition term63 (x0 : real -> Prop) := ~ (all x0).
Definition term119 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))) (real_of_num (NUMERAL 0))).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term45 (x0 : real) := real_mul (real_inv (real_abs x0)).
Definition term59 (x0 : real) := fun y0 : real => (real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0))).
Definition term85 (x0 : real) (x1 : real) := real_mul (real_abs x1) (real_mul (real_inv (real_abs x0)) (real_inv x1)).
Definition term95 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))).
Definition term102 := real_of_num (NUMERAL 0).
Definition term39 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_inv (real_abs x1)).
Definition term40 (x0 : real) (x1 : real) := real_inv (real_div (real_abs x0) (real_abs x1)).
Definition term88 (x0 : real) := real_mul (real_abs x0).
Definition term135 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term108 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))).
Definition term83 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_inv (real_abs x0)) (real_mul (real_abs x1) (real_inv x1))).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term97 (x0 : real) (x1 : real) := real_sub (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))) (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))).
Definition term6 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term65 (x0 : real) := ~ (forall y0 : real, (real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0)))).
Definition term26 (x0 : real) (x1 : real) := real_div (real_sgn x0) (real_sgn x1).
Definition term109 := real_neg (real_of_num (NUMERAL 0)).
Definition term68 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0)))) x1).
Definition term28 (x0 : real) := fun y0 : real => (real_sgn (real_div x0 y0)) = (real_div (real_sgn x0) (real_sgn y0)).
Definition term99 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term51 (x0 : real) := real_mul (real_div x0 (real_abs x0)).
Definition term86 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_inv x1).
Definition term81 (x0 : real) := real_mul (real_abs x0) (real_inv x0).
Definition term127 (x0 : Prop) := exists y0 : real, x0.
Definition term142 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term111 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term62 := forall y0 : real, forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1))).
Definition term35 := forall y0 : real, forall y1 : real, (real_div (real_div y0 y1) (real_div (real_abs y0) (real_abs y1))) = (real_div (real_div y0 (real_abs y0)) (real_div y1 (real_abs y1))).
Definition term34 := forall y0 : real, forall y1 : real, (real_sgn (real_div y0 y1)) = (real_div (real_sgn y0) (real_sgn y1)).
Definition term47 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1)).
Definition term125 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term79 := exists y0 : real, exists y1 : real, ~ ((real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1)))).
Definition term49 (x0 : real) (x1 : real) := real_mul (real_div x0 (real_abs x0)) (real_inv (real_div x1 (real_abs x1))).
Definition term144 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term55 (x0 : real) := real_mul (real_inv x0) (real_inv (real_inv (real_abs x0))).
Definition term43 (x0 : real) := real_inv (real_abs x0).
Definition term74 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul (real_mul y1 (real_inv y2)) (real_mul (real_inv (real_abs y1)) (real_abs y2))) = (real_mul (real_mul y1 (real_inv (real_abs y1))) (real_mul (real_inv y2) (real_abs y2)))) y0).
Definition term66 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_mul x0 (real_inv y1)) (real_mul (real_inv (real_abs x0)) (real_abs y1))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y1) (real_abs y1)))) y0).
Definition term77 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul (real_mul y1 (real_inv y2)) (real_mul (real_inv (real_abs y1)) (real_abs y2))) = (real_mul (real_mul y1 (real_inv (real_abs y1))) (real_mul (real_inv y2) (real_abs y2)))) y0).
Definition term61 := fun y0 : real => forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1))).
Definition term33 := fun y0 : real => forall y1 : real, (real_div (real_div y0 y1) (real_div (real_abs y0) (real_abs y1))) = (real_div (real_div y0 (real_abs y0)) (real_div y1 (real_abs y1))).
Definition term32 := fun y0 : real => forall y1 : real, (real_sgn (real_div y0 y1)) = (real_div (real_sgn y0) (real_sgn y1)).
Definition term101 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term121 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) (x1 : real) := real_sgn (real_div x0 x1).
Definition term52 (x0 : real) := real_mul (real_mul x0 (real_inv (real_abs x0))).
Definition term80 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1))))) (real_of_num (NUMERAL 0))).
Definition term15 (x0 : real) (x1 : real) := real_div (real_abs x0) (real_abs x1).
Definition term130 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term146 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term73 := ~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1)))).
Definition term148 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term110 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term84 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_mul (real_abs x1) (real_inv x1)).
Definition term37 (x0 : real) (x1 : real) := real_mul (real_div x0 x1).
Definition term60 (x0 : real) := forall y0 : real, (real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0))).
Definition term31 (x0 : real) := forall y0 : real, (real_div (real_div x0 y0) (real_div (real_abs x0) (real_abs y0))) = (real_div (real_div x0 (real_abs x0)) (real_div y0 (real_abs y0))).
Definition term131 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term1 (x0 : real) := real_inv (real_inv x0).
Definition term116 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term134 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1)))) x0).
Definition term124 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term46 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_abs x1).
Definition term42 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_inv (real_inv (real_abs x1))).
Definition term140 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term139 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term13 (x0 : real) (x1 : real) := (fun y0 : real => (real_abs (real_div x0 y0)) = (real_div (real_abs x0) (real_abs y0))) x1.
Definition term64 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term57 (x0 : real) := real_mul (real_inv x0) (real_abs x0).
Definition term75 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1)))) x0.
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : real, (real_abs (real_div y0 y1)) = (real_div (real_abs y0) (real_abs y1))) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term147 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term29 (x0 : real) := fun y0 : real => (real_div (real_div x0 y0) (real_div (real_abs x0) (real_abs y0))) = (real_div (real_div x0 (real_abs x0)) (real_div y0 (real_abs y0))).
Definition term24 (x0 : real) := real_div (real_sgn x0).
Definition term100 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term149 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1))))) -> False.
Definition term72 (x0 : real) := exists y0 : real, ~ ((real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0)))).
Definition term48 (x0 : real) (x1 : real) := @eq real (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))).
Definition term16 (x0 : real) := (fun y0 : real => (real_sgn y0) = (real_div y0 (real_abs y0))) x0.
Definition term93 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_mul (real_abs x0) (real_inv (real_abs x1))).
Definition term8 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term106 := real_mul (real_of_num (NUMERAL 0)).
Definition term126 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term107 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))).
Definition term78 := fun y0 : real => exists y1 : real, ~ ((real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1)))).
Definition term38 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x1)).
Definition term138 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term5 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term117 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))).
Definition term132 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term122 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term150 := ((~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1))))) -> False) -> forall y0 : real, forall y1 : real, (real_mul (real_mul y0 (real_inv y1)) (real_mul (real_inv (real_abs y0)) (real_abs y1))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul (real_inv y1) (real_abs y1))).
Definition term19 (x0 : real) (x1 : real) := real_div (real_div x0 x1) (real_abs (real_div x0 x1)).
Definition term69 (x0 : real) (x1 : real) := ~ ((real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))).
Definition term91 (x0 : real) (x1 : real) := real_mul (real_mul x1 (real_inv x0)) (real_mul (real_abs x0) (real_inv (real_abs x1))).
Definition term137 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term27 (x0 : real) (x1 : real) := real_div (real_div x0 (real_abs x0)) (real_div x1 (real_abs x1)).
Definition term71 (x0 : real) := fun y0 : real => ~ ((real_mul (real_mul x0 (real_inv y0)) (real_mul (real_inv (real_abs x0)) (real_abs y0))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y0) (real_abs y0)))).
Definition term54 (x0 : real) := real_inv (real_mul x0 (real_inv (real_abs x0))).
Definition term30 (x0 : real) := forall y0 : real, (real_sgn (real_div x0 y0)) = (real_div (real_sgn x0) (real_sgn y0)).
Definition term12 (x0 : real) := forall y0 : real, (real_abs (real_div x0 y0)) = (real_div (real_abs x0) (real_abs y0)).
Definition term3 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term56 (x0 : real) := real_mul (real_inv x0).
Definition term21 (x0 : real) (x1 : real) := real_div (real_div x0 x1) (real_div (real_abs x0) (real_abs x1)).
Definition term141 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term98 (x0 : real) (x1 : real) := real_add (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 (real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1)))))).
Definition term89 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_mul (real_inv x0) (real_inv (real_abs x1))).
Definition term20 (x0 : real) (x1 : real) := real_div (real_div x0 x1).
Definition term115 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1))))) (real_of_num (NUMERAL 0)).
Definition term118 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)))) (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_mul x0 (real_inv y1)) (real_mul (real_inv (real_abs x0)) (real_abs y1))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv y1) (real_abs y1)))) y0).
Definition term44 (x0 : real) := real_inv (real_inv (real_abs x0)).
Definition term92 (x0 : real) (x1 : real) := real_mul x1 (real_mul (real_inv x0) (real_mul (real_abs x0) (real_inv (real_abs x1)))).
Definition term50 (x0 : real) := real_mul x0 (real_inv (real_abs x0)).
Definition term120 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term136 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term23 (x0 : real) (x1 : real) := @eq real (real_div (real_div x0 x1) (real_div (real_abs x0) (real_abs x1))).
Definition term113 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1))))).
Definition term10 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term22 (x0 : real) (x1 : real) := @eq real (real_sgn (real_div x0 x1)).
Definition term25 (x0 : real) := real_div (real_div x0 (real_abs x0)).
Definition term87 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv (real_abs x1)).
Definition term58 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1)).
Definition term94 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))).
Definition term103 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term145 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term112 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1))))).
Definition term36 (x0 : real) (x1 : real) := real_mul (real_div x0 x1) (real_inv (real_div (real_abs x0) (real_abs x1))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term53 (x0 : real) := real_inv (real_div x0 (real_abs x0)).
Definition term104 := NUMERAL (BIT1 0).
Definition term133 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term123 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term17 (x0 : real) := real_div x0 (real_abs x0).
Definition term143 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x0 (real_inv x1)) (real_mul (real_inv (real_abs x0)) (real_abs x1))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul (real_inv x1) (real_abs x1))).
Definition term114 := real_gt (real_of_num (NUMERAL 0)).
