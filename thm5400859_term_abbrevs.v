Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) /\ ((~ (Peano.le x0 (S x1))) -> (dotdot x0 (S x1)) = (dotdot x0 x1)).
Definition term15 (x0 : nat) (x1 : nat) := imp (Peano.le x0 (S x1)).
Definition term12 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (S x1))) -> (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (dotdot x0 x1).
Definition term7 (x0 : nat) (x1 : nat) := @INSERT nat (S x1) (dotdot x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (dotdot x0 x1).
Definition term1 (x0 : nat -> Prop) (x1 : Prop) (x2 : type993) (x3 : nat -> Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term13 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (S x1))) -> (dotdot x0 (S x1)) = (dotdot x0 x1).
Definition term19 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))).
Definition term18 (x0 : nat) (x1 : nat) := and ((Peano.le x0 (S x1)) -> (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@INSERT nat (S x1) (dotdot x0 x1))).
Definition term16 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat -> Prop) (x4 : nat -> Prop) := (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@COND (nat -> Prop) x2 x3 x4).
Definition term22 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@COND (nat -> Prop) (Peano.le x0 (S x1)) (@INSERT nat (S x1) (dotdot x0 x1)) (dotdot x0 x1))).
Definition term3 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : nat -> Prop) := (x1 -> (fun y0 : nat -> Prop => (dotdot x2 (S x3)) = y0) x0) /\ ((~ x1) -> (fun y0 : nat -> Prop => (dotdot x2 (S x3)) = y0) x4).
Definition term0 (x0 : type993) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat -> Prop) := x0 (@COND (nat -> Prop) x1 x2 x3).
Definition term21 (x0 : nat) (x1 : nat) := @COND (nat -> Prop) (Peano.le x0 (S x1)) (@INSERT nat (S x1) (dotdot x0 x1)) (dotdot x0 x1).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@COND (nat -> Prop) (Peano.le x0 (S x1)) (@INSERT nat (S x1) (dotdot x0 x1)) (dotdot x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0.
Definition term23 (x0 : nat) (x1 : nat) := @eq Prop ((dotdot x0 (S x1)) = (@COND (nat -> Prop) (Peano.le x0 (S x1)) (@INSERT nat (S x1) (dotdot x0 x1)) (dotdot x0 x1))).
Definition term17 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term6 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) -> (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (@INSERT nat (S x1) (dotdot x0 x1))) /\ ((~ (Peano.le x0 (S x1))) -> (fun y0 : nat -> Prop => (dotdot x0 (S x1)) = y0) (dotdot x0 x1)).
Definition term8 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term11 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 (S x1))).
