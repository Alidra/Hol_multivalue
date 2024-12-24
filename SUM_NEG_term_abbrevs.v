Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term73 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term90 (x0 : real) := or (real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term19 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term32 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term52 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term63 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term18 (x0 : nat) := real_neg (real_of_num x0).
Definition term51 := real_of_num (NUMERAL 0).
Definition term58 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term99 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term88 (x0 : real) := real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term125 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term79 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 (x0 : real) := real_sub (real_neg x0).
Definition term46 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0))) x0.
Definition term76 := real_neg (real_of_num (NUMERAL 0)).
Definition term56 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term50 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul x1 (x2 y0)).
Definition term129 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term126 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term72 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term89 (x0 : real) := real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term11 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term75 (x0 : real) := real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x0 x1)).
Definition term4 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1))) x2.
Definition term62 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term20 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term54 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term80 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term1 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term15 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term24 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term78 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term106 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => real_neg (x0 y0).
Definition term57 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term49 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term94 := real_lt (real_of_num (NUMERAL 0)).
Definition term69 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term119 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (y0 y2))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 y1 y0)).
Definition term65 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term33 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term26 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term104 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_neg (x0 x1).
Definition term92 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term47 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : real) := (real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) (real_of_num (NUMERAL 0))).
Definition term101 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term77 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term6 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul x0 (@sum a0 x1 x2).
Definition term114 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_neg (x0 y1))) = (real_neg (@sum a0 y0 x0)).
Definition term53 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 x0 x1).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x1 y0))).
Definition term86 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) (real_of_num (NUMERAL 0)).
Definition term87 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term96 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term41 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term59 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term118 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_neg (y0 y2))) = (real_neg (@sum a0 y1 y0)).
Definition term43 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term39 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term36 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term12 (x0 : real) := real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term30 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term98 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term55 := S (Nat.add 0 0).
Definition term22 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term44 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term17 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term61 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term123 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term127 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term117 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y1))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 y0 x0)).
Definition term2 (a0 : Type') (x0 : a0 -> real) (x1 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0))) x1.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => real_neg (x1 y0))).
Definition term67 := real_mul (real_of_num (NUMERAL 0)).
Definition term93 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term9 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term25 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term121 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (y0 y2))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 y1 y0)).
Definition term120 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_neg (y0 y2))) = (real_neg (@sum a0 y1 y0)).
Definition term35 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term28 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term40 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term71 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x1 y0)).
Definition term7 (x0 : real) := ~ ((real_neg x0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term60 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term34 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term116 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_neg (x0 y1))) = (real_neg (@sum a0 y0 x0)).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_neg (@sum a0 x0 x1).
Definition term81 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term31 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term107 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y0).
Definition term38 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term70 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term27 := real_of_num (NUMERAL (BIT1 0)).
Definition term42 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term74 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term16 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term97 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term91 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term115 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 y1))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (@sum a0 y0 x0)).
Definition term102 (x0 : real) := (~ ((real_neg x0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) -> False.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_neg (x1 y0)).
Definition term83 (x0 : real) := @eq real (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term13 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term95 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term48 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term45 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term23 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term82 := real_div (real_of_num (NUMERAL 0)).
Definition term3 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term68 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term103 (x0 : real) := ((~ ((real_neg x0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) -> False) -> (real_neg x0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term21 := NUMERAL (BIT1 0).
Definition term128 (a0 : Type') := forall y0 : a0 -> real, True.
Definition term124 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term100 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (x0 x1).
Definition term85 := real_gt (real_of_num (NUMERAL 0)).
