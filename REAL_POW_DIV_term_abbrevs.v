Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : real) (x1 : real) (x2 : nat) := real_pow (real_mul x0 x1) x2.
Definition term11 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_pow x0 x2) (real_pow x1 x2).
Definition term26 (x0 : real) (x1 : real) := fun y0 : nat => (real_pow (real_div x0 x1) y0) = (real_div (real_pow x0 y0) (real_pow x1 y0)).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term32 (x0 : real) := fun y0 : real => forall y1 : nat, (real_pow (real_div x0 y0) y1) = (real_div (real_pow x0 y1) (real_pow y0 y1)).
Definition term33 := fun y0 : real => True.
Definition term17 (x0 : real) (x1 : real) := real_pow (real_mul x0 (real_inv x1)).
Definition term21 (x0 : real) (x1 : nat) := real_mul (real_pow x0 x1).
Definition term23 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_pow (real_div x0 x1) x2).
Definition term22 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_pow x0 x2) (real_inv (real_pow x1 x2)).
Definition term35 := forall y0 : real, True.
Definition term36 (x0 : Prop) := forall y0 : real, x0.
Definition term18 (x0 : real) (x1 : real) (x2 : nat) := real_pow (real_div x0 x1) x2.
Definition term14 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term38 := forall y0 : real, forall y1 : real, forall y2 : nat, (real_pow (real_div y0 y1) y2) = (real_div (real_pow y0 y2) (real_pow y1 y2)).
Definition term34 (x0 : real) := forall y0 : real, forall y1 : nat, (real_pow (real_div x0 y0) y1) = (real_div (real_pow x0 y1) (real_pow y0 y1)).
Definition term6 (x0 : real) := forall y0 : real, forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1)).
Definition term25 (x0 : real) (x1 : real) (x2 : nat) := real_div (real_pow x0 x2) (real_pow x1 x2).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1))) x0.
Definition term2 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0))) x1.
Definition term24 (x0 : real) (x1 : real) (x2 : nat) := @eq real (real_mul (real_pow x0 x2) (real_inv (real_pow x1 x2))).
Definition term29 := forall y0 : nat, True.
Definition term16 (x0 : real) (x1 : real) := real_pow (real_div x0 x1).
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term27 := fun y0 : nat => True.
Definition term1 (x0 : real) := forall y0 : nat, (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term9 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0))) x2.
Definition term13 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term20 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_pow x0 x2) (real_pow (real_inv x1) x2).
Definition term19 (x0 : real) (x1 : real) (x2 : nat) := real_pow (real_mul x0 (real_inv x1)) x2.
Definition term37 := fun y0 : real => forall y1 : real, forall y2 : nat, (real_pow (real_div y0 y1) y2) = (real_div (real_pow y0 y2) (real_pow y1 y2)).
Definition term3 (x0 : real) (x1 : nat) := real_pow (real_inv x0) x1.
Definition term28 (x0 : real) (x1 : real) := forall y0 : nat, (real_pow (real_div x0 x1) y0) = (real_div (real_pow x0 y0) (real_pow x1 y0)).
Definition term8 (x0 : real) (x1 : real) := forall y0 : nat, (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0)).
Definition term4 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term31 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : nat, (real_pow (real_mul y0 y1) y2) = (real_mul (real_pow y0 y2) (real_pow y1 y2))) x0.
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1))) x1.
