Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') := @COND (nat -> Prop) ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)) (@EMPTY nat) (dotdot (NUMERAL 0) (Nat.sub (@dimindex a0 (@UNIV a0)) (NUMERAL (BIT1 0)))).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@dimindex a0 x0) = (NUMERAL 0)).
Definition term13 (a0 : Type') := @eq (nat -> Prop) (dotdot (NUMERAL 0) (Nat.sub (@dimindex a0 (@UNIV a0)) (NUMERAL (BIT1 0)))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@dimindex a0 y0) = (NUMERAL 0))) x0.
Definition term12 (a0 : Type') := @eq (nat -> Prop) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (@dimindex a0 (@UNIV a0))) y1)).
Definition term9 (a0 : Type') := @COND (nat -> Prop) ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)) (@EMPTY nat).
Definition term11 (a0 : Type') := @COND (nat -> Prop) False (@EMPTY nat) (dotdot (NUMERAL 0) (Nat.sub (@dimindex a0 (@UNIV a0)) (NUMERAL (BIT1 0)))).
Definition term5 (x0 : nat) := @COND (nat -> Prop) (x0 = (NUMERAL 0)) (@EMPTY nat) (dotdot (NUMERAL 0) (Nat.sub x0 (NUMERAL (BIT1 0)))).
Definition term8 (a0 : Type') := @COND (nat -> Prop) ((@dimindex a0 (@UNIV a0)) = (NUMERAL 0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@dimindex a0 x0) = (NUMERAL 0))) -> ((@dimindex a0 x0) = (NUMERAL 0)) = False.
Definition term10 (a0 : Type') := dotdot (NUMERAL 0) (Nat.sub (@dimindex a0 (@UNIV a0)) (NUMERAL (BIT1 0))).
Definition term3 (x0 : nat) := (fun y0 : nat => (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)) = (@COND (nat -> Prop) (y0 = (NUMERAL 0)) (@EMPTY nat) (dotdot (NUMERAL 0) (Nat.sub y0 (NUMERAL (BIT1 0)))))) x0.
Definition term6 (a0 : Type') := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 (@dimindex a0 (@UNIV a0))) y1).
Definition term4 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1).
