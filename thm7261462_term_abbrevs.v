Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) (x3 : nat) := (fun y0 : nat => (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 y0)) -> (x0 y1) = (x2 y1)) -> (@sum nat (dotdot x1 y0) (fun y1 : nat => x0 y1)) = (@sum nat (dotdot x1 y0) x2)) x3.
Definition term1 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> (x0 y0) = (x3 y0)) -> (@sum nat (dotdot x1 x2) (fun y0 : nat => x0 y0)) = (@sum nat (dotdot x1 x2) x3).
