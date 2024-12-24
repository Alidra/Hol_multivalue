Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) (x1 : nat) := ((Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1))) /\ ((~ (Peano.le x0 (S x1))) -> (dotdot x0 (S x1)) = (dotdot x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := @INSERT nat (S x1) (dotdot x0 x1).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 (S x1)).
Definition term1 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
Definition term2 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (S x1))) -> (dotdot x0 (S x1)) = (dotdot x0 x1).
Definition term7 (x0 : nat) (x1 : nat) := @COND (nat -> Prop) (Peano.le x0 (S x1)) (@INSERT nat (S x1) (dotdot x0 x1)) (dotdot x0 x1).
Definition term5 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
