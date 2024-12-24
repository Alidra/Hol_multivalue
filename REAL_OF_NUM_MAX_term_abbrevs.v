Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : a0, (@COND a1 x0 (y0 y1) (y0 y2)) = (y0 (@COND a0 x0 y1 y2))) x1.
Definition term48 (x0 : nat) := fun y0 : nat => (real_max (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.max x0 y0)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : Prop) := fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : a0, (@COND a1 x0 (y0 y1) (y0 y2)) = (y0 (@COND a0 x0 y1 y2)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : Prop) := fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : a0, (y0 (@COND a0 x0 y1 y2)) = (@COND a1 x0 (y0 y1) (y0 y2)).
Definition term35 (x0 : nat) (x1 : nat) := @COND real (real_le (real_of_num x1) (real_of_num x0)) (real_of_num x0) (real_of_num x1).
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term31 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) := forall y0 : a0, (x2 (@COND a0 x0 x1 y0)) = (@COND a1 x0 (x2 x1) (x2 y0)).
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.max x0 y0) = (@COND nat (Peano.le x0 y0) y0 x0)) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) := fun y0 : a0 => (x2 (@COND a0 x0 x1 y0)) = (@COND a1 x0 (x2 x1) (x2 y0)).
Definition term37 (x0 : nat -> real) (x1 : Prop) (x2 : nat) (x3 : nat) := x0 (@COND nat x1 x2 x3).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, (@COND a1 x1 (x0 y0) (x0 y1)) = (x0 (@COND a0 x1 y0 y1))) x2.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) := fun y0 : a0 => forall y1 : a0, (@COND a1 x1 (x0 y0) (x0 y1)) = (x0 (@COND a0 x1 y0 y1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) (x3 : a0) := x0 (@COND a0 x1 x2 x3).
Definition term27 (x0 : nat) := forall y0 : nat, (Nat.max x0 y0) = (@COND nat (Peano.le x0 y0) y0 x0).
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) (x3 : a0) := @COND a1 x0 (x2 x1) (x2 x3).
Definition term55 := forall y0 : nat, forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1)).
Definition term25 (x0 : real) (x1 : real) := @COND real (real_le x1 x0) x0 x1.
Definition term36 (x0 : Prop) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @COND real x0 (x2 x1) (x2 x3).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) := fun y0 : a0 => (@COND a1 x1 (x0 x2) (x0 y0)) = (x0 (@COND a0 x1 x2 y0)).
Definition term43 (x0 : nat) (x1 : nat) := @COND nat (real_le (real_of_num x1) (real_of_num x0)) x0 x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) := fun y0 : a0 => forall y1 : a0, (x1 (@COND a0 x0 y0 y1)) = (@COND a1 x0 (x1 y0) (x1 y1)).
Definition term51 := forall y0 : nat, True.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) := forall y0 : a0, (@COND a1 x1 (x0 x2) (x0 y0)) = (x0 (@COND a0 x1 x2 y0)).
Definition term15 (a0 : Type') (a1 : Type') := fun y0 : Prop => forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (@COND a1 y0 (y1 y2) (y1 y3)) = (y1 (@COND a0 y0 y2 y3)).
Definition term14 (a0 : Type') (a1 : Type') := fun y0 : Prop => forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (y1 (@COND a0 y0 y2 y3)) = (@COND a1 y0 (y1 y2) (y1 y3)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (@COND a1 y0 (y1 y2) (y1 y3)) = (y1 (@COND a0 y0 y2 y3))) x0.
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_max y1 y0) = (@COND real (real_le y1 y0) y0 y1)) x0.
Definition term49 := fun y0 : nat => True.
Definition term44 (x0 : nat) (x1 : nat) := real_of_num (@COND nat (Peano.le x1 x0) x0 x1).
Definition term38 (x0 : nat) (x1 : nat) := real_of_num (@COND nat (real_le (real_of_num x1) (real_of_num x0)) x0 x1).
Definition term17 (a0 : Type') (a1 : Type') := forall y0 : Prop, forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (@COND a1 y0 (y1 y2) (y1 y3)) = (y1 (@COND a0 y0 y2 y3)).
Definition term16 (a0 : Type') (a1 : Type') := forall y0 : Prop, forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (y1 (@COND a0 y0 y2 y3)) = (@COND a1 y0 (y1 y2) (y1 y3)).
Definition term41 (x0 : nat) (x1 : nat) := @COND nat (real_le (real_of_num x0) (real_of_num x1)) x1.
Definition term47 (x0 : nat) (x1 : nat) := real_of_num (Nat.max x0 x1).
Definition term45 (x0 : nat) (x1 : nat) := @eq real (real_max (real_of_num x0) (real_of_num x1)).
Definition term23 (x0 : real) := forall y0 : real, (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0).
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.max y0 y1) = (@COND nat (Peano.le y0 y1) y1 y0)) x0.
Definition term39 (x0 : nat) (x1 : nat) := @COND nat (real_le (real_of_num x0) (real_of_num x1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) := forall y0 : a0, forall y1 : a0, (@COND a1 x1 (x0 y0) (x0 y1)) = (x0 (@COND a0 x1 y0 y1)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, (x1 (@COND a0 x0 y0 y1)) = (@COND a1 x0 (x1 y0) (x1 y1)).
Definition term50 (x0 : nat) := forall y0 : nat, (real_max (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.max x0 y0)).
Definition term46 (x0 : nat) (x1 : nat) := @eq real (real_of_num (@COND nat (Peano.le x1 x0) x0 x1)).
Definition term40 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1).
Definition term53 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : a0, (@COND a1 x0 (y0 y1) (y0 y2)) = (y0 (@COND a0 x0 y1 y2)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : a0, (y0 (@COND a0 x0 y1 y2)) = (@COND a1 x0 (y0 y1) (y0 y2)).
Definition term54 := fun y0 : nat => forall y1 : nat, (real_max (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.max y0 y1)).
Definition term33 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term42 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1) x1.
Definition term34 (x0 : nat) (x1 : nat) := real_max (real_of_num x0) (real_of_num x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (@COND a1 x1 (x0 x2) (x0 y0)) = (x0 (@COND a0 x1 x2 y0))) x3.
Definition term29 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) x0 x1.
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0)) x1.
