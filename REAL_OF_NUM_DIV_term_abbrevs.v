Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term125 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term109 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term146 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))) (real_of_num (NUMERAL 0))).
Definition term50 (x0 : nat) (x1 : nat) := real_mul (real_of_num (Nat.modulo x0 x1)).
Definition term26 := real_of_num (NUMERAL 0).
Definition term53 (x0 : nat) (x1 : nat) := real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1)).
Definition term48 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term121 (x0 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term115 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))))).
Definition term78 (x0 : nat) (x1 : nat) := real_mul (real_of_num x1) (real_div (real_of_num x0) (real_of_num x1)).
Definition term19 := (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1) -> forall y0 : real, forall y1 : real, (exists y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1.
Definition term151 (x0 : nat) (x1 : nat) := (~ ((real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))) -> False.
Definition term41 := real_inv (real_of_num (NUMERAL 0)).
Definition term92 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x1 (real_sub x0 y0)) = (real_sub (real_mul x1 x0) (real_mul x1 y0))) x2.
Definition term57 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term136 := real_neg (real_of_num (NUMERAL 0)).
Definition term101 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term153 (x0 : nat) (x1 : nat) := exists y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 (real_of_num (Nat.div x0 x1))) = (real_mul y0 (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))))).
Definition term9 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1))) -> x0 = x1.
Definition term135 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term120 (x0 : nat) (x1 : nat) := real_add (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0))) (real_add (real_of_num x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term138 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_sub y0 y1)) = (real_sub (real_mul x0 y0) (real_mul x0 y1)).
Definition term18 := forall y0 : real, forall y1 : real, (exists y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1.
Definition term7 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0.
Definition term5 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1.
Definition term154 (x0 : nat) (x1 : nat) := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 (real_of_num (Nat.div x0 x1))) = (real_mul y0 (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))))).
Definition term13 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1) -> x0 = x1.
Definition term106 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 (x0 : nat) (x1 : nat) := real_mul (real_of_num x1) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1)).
Definition term81 (x0 : nat) (x1 : nat) := (~ ((real_of_num x1) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_of_num x1) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))) = (real_of_num (Nat.modulo x0 x1)).
Definition term85 (x0 : nat) (x1 : nat) := real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1)).
Definition term102 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1)))).
Definition term24 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term63 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term4 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)).
Definition term68 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x1 (real_sub x0 y0)) = (real_sub (real_mul x1 x0) (real_mul x1 y0)).
Definition term47 (x0 : nat) (x1 : nat) := real_mul (real_of_num (Nat.modulo x0 x1)) (real_inv (real_of_num x1)).
Definition term93 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1)))).
Definition term33 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term155 (x0 : nat) := forall y0 : nat, (real_of_num (Nat.div x0 y0)) = (real_sub (real_div (real_of_num x0) (real_of_num y0)) (real_div (real_of_num (Nat.modulo x0 y0)) (real_of_num y0))).
Definition term1 (x0 : nat) := forall y0 : nat, (real_of_num (Nat.modulo x0 y0)) = (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 y0)) (real_of_num y0))).
Definition term40 (x0 : nat) := real_inv (real_of_num x0).
Definition term123 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term110 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term148 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term88 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))).
Definition term90 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))) (real_of_num (NUMERAL 0))).
Definition term150 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term137 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) := forall y0 : real, (exists y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0.
Definition term45 := real_sub (real_of_num (NUMERAL 0)).
Definition term37 := @eq real (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term144 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))).
Definition term49 (x0 : nat) := real_of_num (Nat.modulo x0 (NUMERAL 0)).
Definition term84 (x0 : nat) (x1 : nat) := @eq real (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term75 (x0 : nat) (x1 : nat) := real_mul (real_of_num x1) (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))).
Definition term83 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_of_num (Nat.modulo x0 x1)).
Definition term143 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term132 (x0 : nat) (x1 : nat) := real_add (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1)))).
Definition term99 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term156 := forall y0 : nat, forall y1 : nat, (real_of_num (Nat.div y0 y1)) = (real_sub (real_div (real_of_num y0) (real_of_num y1)) (real_div (real_of_num (Nat.modulo y0 y1)) (real_of_num y1))).
Definition term91 (x0 : nat) (x1 : nat) := real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1).
Definition term52 (x0 : nat) := real_mul (real_of_num (Nat.modulo x0 (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term119 (x0 : nat) (x1 : nat) := real_add (real_of_num x1) (real_add (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term23 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term55 (x0 : nat) (x1 : nat) := (exists y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 (real_of_num (Nat.div x0 x1))) = (real_mul y0 (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1)))))) -> (real_of_num (Nat.div x0 x1)) = (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))).
Definition term74 (x0 : nat) := and (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))).
Definition term112 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term116 (x0 : nat) (x1 : nat) := real_add (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term94 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0)))) (real_of_num x1).
Definition term59 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul y1 (real_div y0 y1)) = y0) x0.
Definition term29 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1) x0.
Definition term149 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term42 (x0 : nat) := real_mul (real_of_num x0).
Definition term77 (x0 : nat) (x1 : nat) := (~ ((real_of_num x0) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_of_num x0) (real_div (real_of_num x1) (real_of_num x0))) = (real_of_num x1).
Definition term100 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term35 (x0 : nat) (x1 : nat) := real_of_num (Nat.div x0 x1).
Definition term62 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_div x1 x0)) = x1.
Definition term38 (x0 : nat) (x1 : nat) := real_div (real_of_num x0) (real_of_num x1).
Definition term30 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term126 := real_mul (real_of_num (NUMERAL 0)).
Definition term133 (x0 : nat) (x1 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term134 (x0 : nat) (x1 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_sub y0 y1)) = (real_sub (real_mul x0 y0) (real_mul x0 y1))) x1.
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0) x1.
Definition term44 (x0 : nat) (x1 : nat) := real_sub (real_div (real_of_num x0) (real_of_num x1)).
Definition term117 (x0 : nat) (x1 : nat) := real_add (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term113 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term73 (x0 : nat) := ~ ((real_of_num x0) = (real_of_num (NUMERAL 0))).
Definition term130 (x0 : nat) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))).
Definition term131 (x0 : nat) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term95 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term103 (x0 : nat) (x1 : nat) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x1 x0) = (real_mul x1 x2)).
Definition term80 (x0 : nat) := real_sub (real_of_num x0).
Definition term46 (x0 : nat) (x1 : nat) := real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1).
Definition term56 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_of_num (Nat.modulo y0 y1)) = (real_sub (real_of_num y0) (real_mul (real_of_num (Nat.div y0 y1)) (real_of_num y1)))) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_of_num (Nat.modulo x0 y0)) = (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 y0)) (real_of_num y0)))) x1.
Definition term114 (x0 : nat) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term128 (x0 : nat) (x1 : nat) := real_add (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_of_num (NUMERAL 0)).
Definition term104 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term152 (x0 : nat) (x1 : nat) := ((~ ((real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))) -> False) -> (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))).
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y1 x0) = (real_mul y1 y0))) -> x0 = y0) x1.
Definition term118 (x0 : nat) := real_add (real_of_num x0).
Definition term122 (x0 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term39 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_inv (real_of_num x1)).
Definition term51 (x0 : nat) := real_mul (real_of_num (Nat.modulo x0 (NUMERAL 0))).
Definition term107 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term76 (x0 : nat) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_div (real_of_num x0) (real_of_num x1))) (real_mul (real_of_num x1) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))).
Definition term60 (x0 : real) := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0.
Definition term127 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term111 := real_of_num (NUMERAL (BIT1 0)).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_sub x1 x2).
Definition term129 (x0 : nat) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))).
Definition term79 (x0 : nat) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_div (real_of_num x0) (real_of_num x1))).
Definition term72 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term71 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x1 x0) (real_mul x1 x2).
Definition term142 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))) (real_of_num (NUMERAL 0)).
Definition term145 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))) (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.div x0 x1)).
Definition term147 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term61 (x0 : real) (x1 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_div x0 y0)) = x0) x1.
Definition term105 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term140 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))).
Definition term32 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term14 (x0 : real) (x1 : real) := exists y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1)).
Definition term97 (x0 : nat) (x1 : nat) := real_add (real_of_num x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0)))) (real_of_num x1))).
Definition term15 (x0 : real) (x1 : real) := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1)).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x1) = (real_mul x0 x2))) -> x1 = x2.
Definition term89 (x0 : nat) (x1 : nat) := ~ ((real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1))))).
Definition term16 (x0 : real) (x1 : real) := (exists y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1))) -> x0 = x1.
Definition term124 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term96 (x0 : nat) (x1 : nat) := real_sub (real_of_num x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0)))) (real_of_num x1)).
Definition term34 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term25 (x0 : real) := (fun y0 : real => (real_sub y0 y0) = (real_of_num (NUMERAL 0))) x0.
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term87 (x0 : nat) (x1 : nat) := True /\ ((real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_sub (real_of_num x0) (real_of_num (Nat.modulo x0 x1)))).
Definition term139 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) (real_sub (real_of_num x0) (real_sub (real_of_num x0) (real_mul (real_of_num (Nat.div x0 x1)) (real_of_num x1)))))).
Definition term65 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_sub y1 y2)) = (real_sub (real_mul y0 y1) (real_mul y0 y2))) x0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y2 y0) = (real_mul y2 y1))) -> y0 = y1) x0.
Definition term3 (x0 : nat) (x1 : nat) := real_of_num (Nat.modulo x0 x1).
Definition term64 (x0 : real) (x1 : real) := real_mul x1 (real_div x0 x1).
Definition term22 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term86 (x0 : nat) (x1 : nat) := (~ ((real_of_num x1) = (real_of_num (NUMERAL 0)))) /\ ((real_mul (real_of_num x1) (real_of_num (Nat.div x0 x1))) = (real_mul (real_of_num x1) (real_sub (real_div (real_of_num x0) (real_of_num x1)) (real_div (real_of_num (Nat.modulo x0 x1)) (real_of_num x1))))).
Definition term98 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_num (Nat.div x1 x0)))) (real_of_num x1)).
Definition term108 := NUMERAL (BIT1 0).
Definition term54 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term43 (x0 : nat) := real_mul (real_of_num x0) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 x0) = (real_mul y0 x1))) -> x0 = x1) x2.
Definition term141 := real_gt (real_of_num (NUMERAL 0)).
