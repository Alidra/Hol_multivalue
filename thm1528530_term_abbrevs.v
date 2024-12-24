Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term25 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term19 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term31 := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term11 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term42 := (fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term89 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term104 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term29 := real_of_num (NUMERAL 0).
Definition term39 := (fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term98 := real_sub (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term41 := fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term103 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term106 := real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term86 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term68 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term117 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term122 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 := and (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term38 := (real_gt (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term46 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_gt (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term55 := @eq Prop (real_gt (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term73 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term9 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term113 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term49 := and (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term60 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term23 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term5 := real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term48 := real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term43 := real_gt (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term35 := real_gt (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term47 := (fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term112 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1) x2.
Definition term126 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term90 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term69 := real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term79 := (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term1 := (real_gt (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term131 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term61 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term70 := real_sub (real_of_num (NUMERAL 0)).
Definition term107 := real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term87 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term78 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term51 := (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term97 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term80 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term100 := real_sub (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term71 := real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term127 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term33 := real_gt (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term40 := ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term65 := real_ge (real_of_num (NUMERAL (BIT1 0))).
Definition term83 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 := ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_gt (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term56 := real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term30 := real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term115 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term111 := ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term28 := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term130 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term81 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term34 := real_gt (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term44 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term27 := real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term2 := real_abs (real_of_num (NUMERAL (BIT1 0))).
Definition term17 := real_neg (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term121 := real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term96 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term8 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term18 := real_neg (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term128 := or (((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term63 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term52 := or ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term26 := @eq real (real_neg (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term0 := ~ ((real_abs (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term94 := NUMERAL (BIT0 (BIT1 0)).
Definition term123 := real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term118 := real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term58 := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term99 := real_sub (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term114 := (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term119 := real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term50 := (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt (real_add y0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term91 := Nat.add (BIT1 0) (BIT1 0).
Definition term16 := real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 := real_ge (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term21 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term59 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term133 := (~ ((real_abs (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term20 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term13 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term101 := real_sub (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term3 := real_of_num (NUMERAL (BIT1 0)).
Definition term92 := BIT0 (BIT1 0).
Definition term37 := or (real_gt (real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term36 := or (real_gt (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term116 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term110 := or ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term62 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term102 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term53 := or ((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term67 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term129 := (((real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term109 := (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term88 := real_gt (real_sub (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term66 := real_gt (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term95 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term24 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))).
Definition term22 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term75 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term125 := and (real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term85 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 := real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term124 := real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term120 := real_gt (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term64 := real_ge (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term15 := real_add (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 := real_gt (real_sub (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term76 := real_gt (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term74 := real_add (real_of_num (NUMERAL 0)).
Definition term32 := real_gt (real_sub (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 := NUMERAL (BIT1 0).
Definition term72 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term77 := real_gt (real_of_num (NUMERAL 0)).
