Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@COND (nat -> Prop) (x0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat)).
Definition term11 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@EMPTY nat).
Definition term3 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat -> Prop) := (x1 -> (fun y0 : nat -> Prop => (dotdot x2 (NUMERAL 0)) = y0) x0) /\ ((~ x1) -> (fun y0 : nat -> Prop => (dotdot x2 (NUMERAL 0)) = y0) x3).
Definition term10 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term19 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (dotdot x0 (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ ((~ (x0 = (NUMERAL 0))) -> (dotdot x0 (NUMERAL 0)) = (@EMPTY nat)).
Definition term22 (x0 : nat) := @eq Prop ((dotdot x0 (NUMERAL 0)) = (@COND (nat -> Prop) (x0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat))).
Definition term4 (x0 : nat) := fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0.
Definition term8 (x0 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@EMPTY nat).
Definition term1 (x0 : nat -> Prop) (x1 : Prop) (x2 : type993) (x3 : nat -> Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term14 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term13 (x0 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
Definition term18 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (dotdot x0 (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term2 (x0 : nat) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat -> Prop) := (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@COND (nat -> Prop) x1 x2 x3).
Definition term21 (x0 : nat) := @eq Prop ((fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@COND (nat -> Prop) (x0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat))).
Definition term12 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (dotdot x0 (NUMERAL 0)) = (@EMPTY nat).
Definition term16 (x0 : nat) := (x0 = (NUMERAL 0)) -> (dotdot x0 (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
Definition term0 (x0 : type993) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat -> Prop) := x0 (@COND (nat -> Prop) x1 x2 x3).
Definition term17 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term20 (x0 : nat) := @COND (nat -> Prop) (x0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat).
Definition term7 := @INSERT nat (NUMERAL 0) (@EMPTY nat).
Definition term6 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@EMPTY nat)).
Definition term9 (x0 : nat) := dotdot x0 (NUMERAL 0).
Definition term15 (x0 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : nat -> Prop => (dotdot x0 (NUMERAL 0)) = y0) (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
