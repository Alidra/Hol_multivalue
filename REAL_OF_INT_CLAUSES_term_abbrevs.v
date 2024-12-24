Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term139 (x0 : int) := forall y0 : int, (real_mul (real_of_int x0) (real_of_int y0)) = (real_of_int (int_mul x0 y0)).
Definition term133 (x0 : int) := forall y0 : int, (real_sub (real_of_int x0) (real_of_int y0)) = (real_of_int (int_sub x0 y0)).
Definition term127 (x0 : int) := forall y0 : int, (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0)).
Definition term102 (x0 : int) := forall y0 : int, (real_min (real_of_int x0) (real_of_int y0)) = (real_of_int (int_min x0 y0)).
Definition term96 (x0 : int) := forall y0 : int, (real_max (real_of_int x0) (real_of_int y0)) = (real_of_int (int_max x0 y0)).
Definition term13 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term14 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term22 (x0 : int) := real_sgn (real_of_int x0).
Definition term52 (x0 : int) (x1 : int) := real_gt (real_of_int x0) (real_of_int x1).
Definition term71 (x0 : int) := fun y0 : int => (real_ge (real_of_int x0) (real_of_int y0)) = (int_ge x0 y0).
Definition term125 (x0 : int) (x1 : int) := @eq real (real_add (real_of_int x0) (real_of_int x1)).
Definition term156 := (forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))))))).
Definition term155 := (forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))))).
Definition term154 := (forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))))).
Definition term9 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term89 (x0 : int) := fun y0 : int => (real_lt (real_of_int x0) (real_of_int y0)) = (int_lt x0 y0).
Definition term65 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term62 := fun y0 : int => True.
Definition term57 (x0 : int) := (fun y0 : int => forall y1 : int, (y0 = y1) = ((real_of_int y0) = (real_of_int y1))) x0.
Definition term53 (x0 : int) := (fun y0 : int => forall y1 : int, (int_ge y0 y1) = (real_ge (real_of_int y0) (real_of_int y1))) x0.
Definition term49 (x0 : int) := (fun y0 : int => forall y1 : int, (int_gt y0 y1) = (real_gt (real_of_int y0) (real_of_int y1))) x0.
Definition term45 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = (real_le (real_of_int y0) (real_of_int y1))) x0.
Definition term41 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (real_lt (real_of_int y0) (real_of_int y1))) x0.
Definition term28 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_max y0 y1)) = (real_max (real_of_int y0) (real_of_int y1))) x0.
Definition term23 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_min y0 y1)) = (real_min (real_of_int y0) (real_of_int y1))) x0.
Definition term15 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1))) x0.
Definition term10 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_sub y0 y1)) = (real_sub (real_of_int y0) (real_of_int y1))) x0.
Definition term5 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_mul y0 y1)) = (real_mul (real_of_int y0) (real_of_int y1))) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : nat, (real_of_int (int_pow y0 y1)) = (real_pow (real_of_int y0) y1)) x0.
Definition term137 (x0 : int) (x1 : int) := @eq real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term142 := and (forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))).
Definition term136 := and (forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))).
Definition term130 := and (forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))).
Definition term105 := and (forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))).
Definition term99 := and (forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))).
Definition term93 := and (forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)).
Definition term87 := and (forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)).
Definition term81 := and (forall y0 : int, forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1)).
Definition term75 := and (forall y0 : int, forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1)).
Definition term69 := and (forall y0 : int, forall y1 : int, ((real_of_int y0) = (real_of_int y1)) = (y0 = y1)).
Definition term36 (x0 : int) := (fun y0 : int => (real_of_int (int_neg y0)) = (real_neg (real_of_int y0))) x0.
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0))) x1.
Definition term26 (x0 : int) (x1 : int) := real_of_int (int_min x0 x1).
Definition term144 (x0 : int) := fun y0 : nat => (real_pow (real_of_int x0) y0) = (real_of_int (int_pow x0 y0)).
Definition term131 (x0 : int) (x1 : int) := @eq real (real_sub (real_of_int x0) (real_of_int x1)).
Definition term90 (x0 : int) := forall y0 : int, (real_lt (real_of_int x0) (real_of_int y0)) = (int_lt x0 y0).
Definition term84 (x0 : int) := forall y0 : int, (real_le (real_of_int x0) (real_of_int y0)) = (int_le x0 y0).
Definition term78 (x0 : int) := forall y0 : int, (real_gt (real_of_int x0) (real_of_int y0)) = (int_gt x0 y0).
Definition term72 (x0 : int) := forall y0 : int, (real_ge (real_of_int x0) (real_of_int y0)) = (int_ge x0 y0).
Definition term63 (x0 : int) := forall y0 : int, ((real_of_int x0) = (real_of_int y0)) = (x0 = y0).
Definition term70 (x0 : int) (x1 : int) := @eq Prop (real_ge (real_of_int x0) (real_of_int x1)).
Definition term106 (x0 : nat) := @eq real (real_of_num x0).
Definition term34 (x0 : int) := real_of_int (int_abs x0).
Definition term58 (x0 : int) := forall y0 : int, (x0 = y0) = ((real_of_int x0) = (real_of_int y0)).
Definition term54 (x0 : int) := forall y0 : int, (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0)).
Definition term50 (x0 : int) := forall y0 : int, (int_gt x0 y0) = (real_gt (real_of_int x0) (real_of_int y0)).
Definition term46 (x0 : int) := forall y0 : int, (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0)).
Definition term42 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0)).
Definition term29 (x0 : int) := forall y0 : int, (real_of_int (int_max x0 y0)) = (real_max (real_of_int x0) (real_of_int y0)).
Definition term24 (x0 : int) := forall y0 : int, (real_of_int (int_min x0 y0)) = (real_min (real_of_int x0) (real_of_int y0)).
Definition term16 (x0 : int) := forall y0 : int, (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term11 (x0 : int) := forall y0 : int, (real_of_int (int_sub x0 y0)) = (real_sub (real_of_int x0) (real_of_int y0)).
Definition term6 (x0 : int) := forall y0 : int, (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0)).
Definition term140 := fun y0 : int => forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1)).
Definition term134 := fun y0 : int => forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1)).
Definition term128 := fun y0 : int => forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1)).
Definition term103 := fun y0 : int => forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1)).
Definition term97 := fun y0 : int => forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1)).
Definition term18 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term150 := (forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))).
Definition term107 := fun y0 : nat => (real_of_num y0) = (real_of_int (int_of_num y0)).
Definition term148 := (forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))).
Definition term101 (x0 : int) := fun y0 : int => (real_min (real_of_int x0) (real_of_int y0)) = (real_of_int (int_min x0 y0)).
Definition term94 (x0 : int) (x1 : int) := @eq real (real_max (real_of_int x0) (real_of_int x1)).
Definition term146 := fun y0 : int => forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)).
Definition term149 := (forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))).
Definition term163 := (forall y0 : int, forall y1 : int, ((real_of_int y0) = (real_of_int y1)) = (y0 = y1)) /\ ((forall y0 : int, forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))))))))))))).
Definition term162 := (forall y0 : int, forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))))))))))))).
Definition term161 := (forall y0 : int, forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))))))))))).
Definition term160 := (forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))))))))))).
Definition term159 := (forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))))))))).
Definition term158 := (forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))))))))).
Definition term157 := (forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))) /\ ((forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))) /\ ((forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))) /\ ((forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))))))).
Definition term153 := (forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))))).
Definition term152 := (forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1))) /\ ((forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1))))))).
Definition term40 (x0 : nat) := real_of_int (int_of_num x0).
Definition term25 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_min x0 y0)) = (real_min (real_of_int x0) (real_of_int y0))) x1.
Definition term145 (x0 : int) := forall y0 : nat, (real_pow (real_of_int x0) y0) = (real_of_int (int_pow x0 y0)).
Definition term19 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term117 (x0 : int) := @eq real (real_abs (real_of_int x0)).
Definition term112 := and (forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0))).
Definition term44 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term83 (x0 : int) := fun y0 : int => (real_le (real_of_int x0) (real_of_int y0)) = (int_le x0 y0).
Definition term20 (x0 : int) := (fun y0 : int => (real_of_int (int_sgn y0)) = (real_sgn (real_of_int y0))) x0.
Definition term39 (x0 : nat) := (fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0)) x0.
Definition term33 (x0 : int) := (fun y0 : int => (real_of_int (int_abs y0)) = (real_abs (real_of_int y0))) x0.
Definition term88 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_of_int x0) (real_of_int x1)).
Definition term12 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_sub x0 y0)) = (real_sub (real_of_int x0) (real_of_int y0))) x1.
Definition term109 := forall y0 : nat, (real_of_num y0) = (real_of_int (int_of_num y0)).
Definition term110 := forall y0 : nat, True.
Definition term77 (x0 : int) := fun y0 : int => (real_gt (real_of_int x0) (real_of_int y0)) = (int_gt x0 y0).
Definition term66 (x0 : Prop) := forall y0 : int, x0.
Definition term56 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int x1).
Definition term118 := fun y0 : int => (real_abs (real_of_int y0)) = (real_of_int (int_abs y0)).
Definition term147 := forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)).
Definition term141 := forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1)).
Definition term135 := forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1)).
Definition term129 := forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1)).
Definition term104 := forall y0 : int, forall y1 : int, (real_min (real_of_int y0) (real_of_int y1)) = (real_of_int (int_min y0 y1)).
Definition term98 := forall y0 : int, forall y1 : int, (real_max (real_of_int y0) (real_of_int y1)) = (real_of_int (int_max y0 y1)).
Definition term92 := forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1).
Definition term86 := forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1).
Definition term80 := forall y0 : int, forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1).
Definition term74 := forall y0 : int, forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1).
Definition term68 := forall y0 : int, forall y1 : int, ((real_of_int y0) = (real_of_int y1)) = (y0 = y1).
Definition term122 := fun y0 : int => (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0)).
Definition term4 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term108 := fun y0 : nat => True.
Definition term123 := forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0)).
Definition term119 := forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0)).
Definition term115 := forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0)).
Definition term126 (x0 : int) := fun y0 : int => (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0)).
Definition term91 := fun y0 : int => forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1).
Definition term85 := fun y0 : int => forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1).
Definition term79 := fun y0 : int => forall y1 : int, (real_gt (real_of_int y0) (real_of_int y1)) = (int_gt y0 y1).
Definition term73 := fun y0 : int => forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1).
Definition term67 := fun y0 : int => forall y1 : int, ((real_of_int y0) = (real_of_int y1)) = (y0 = y1).
Definition term21 (x0 : int) := real_of_int (int_sgn x0).
Definition term121 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term31 (x0 : int) (x1 : int) := real_of_int (int_max x0 x1).
Definition term100 (x0 : int) (x1 : int) := @eq real (real_min (real_of_int x0) (real_of_int x1)).
Definition term132 (x0 : int) := fun y0 : int => (real_sub (real_of_int x0) (real_of_int y0)) = (real_of_int (int_sub x0 y0)).
Definition term38 (x0 : int) := real_neg (real_of_int x0).
Definition term114 := fun y0 : int => (real_neg (real_of_int y0)) = (real_of_int (int_neg y0)).
Definition term64 := forall y0 : int, True.
Definition term59 (x0 : int) (x1 : int) := (fun y0 : int => (x0 = y0) = ((real_of_int x0) = (real_of_int y0))) x1.
Definition term124 := and (forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))).
Definition term120 := and (forall y0 : int, (real_abs (real_of_int y0)) = (real_of_int (int_abs y0))).
Definition term116 := and (forall y0 : int, (real_neg (real_of_int y0)) = (real_of_int (int_neg y0))).
Definition term48 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term51 (x0 : int) (x1 : int) := (fun y0 : int => (int_gt x0 y0) = (real_gt (real_of_int x0) (real_of_int y0))) x1.
Definition term113 (x0 : int) := @eq real (real_neg (real_of_int x0)).
Definition term76 (x0 : int) (x1 : int) := @eq Prop (real_gt (real_of_int x0) (real_of_int x1)).
Definition term82 (x0 : int) (x1 : int) := @eq Prop (real_le (real_of_int x0) (real_of_int x1)).
Definition term61 (x0 : int) := fun y0 : int => ((real_of_int x0) = (real_of_int y0)) = (x0 = y0).
Definition term30 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_max x0 y0)) = (real_max (real_of_int x0) (real_of_int y0))) x1.
Definition term143 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) x1).
Definition term43 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0))) x1.
Definition term27 (x0 : int) (x1 : int) := real_min (real_of_int x0) (real_of_int x1).
Definition term111 (x0 : Prop) := forall y0 : nat, x0.
Definition term1 (x0 : int) := forall y0 : nat, (real_of_int (int_pow x0 y0)) = (real_pow (real_of_int x0) y0).
Definition term8 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term37 (x0 : int) := real_of_int (int_neg x0).
Definition term7 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0))) x1.
Definition term47 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0))) x1.
Definition term35 (x0 : int) := real_abs (real_of_int x0).
Definition term3 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term151 := (forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0))) /\ ((forall y0 : int, forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_sub (real_of_int y0) (real_of_int y1)) = (real_of_int (int_sub y0 y1))) /\ ((forall y0 : int, forall y1 : int, (real_mul (real_of_int y0) (real_of_int y1)) = (real_of_int (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : nat, (real_pow (real_of_int y0) y1) = (real_of_int (int_pow y0 y1)))))).
Definition term32 (x0 : int) (x1 : int) := real_max (real_of_int x0) (real_of_int x1).
Definition term55 (x0 : int) (x1 : int) := (fun y0 : int => (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0))) x1.
Definition term95 (x0 : int) := fun y0 : int => (real_max (real_of_int x0) (real_of_int y0)) = (real_of_int (int_max x0 y0)).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_of_int (int_pow x0 y0)) = (real_pow (real_of_int x0) y0)) x1.
Definition term60 (x0 : int) (x1 : int) := @eq Prop ((real_of_int x0) = (real_of_int x1)).
Definition term138 (x0 : int) := fun y0 : int => (real_mul (real_of_int x0) (real_of_int y0)) = (real_of_int (int_mul x0 y0)).
