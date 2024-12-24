Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := forall y0 : nat, (dotdot x0 (S y0)) = (@COND (nat -> Prop) (Peano.le x0 (S y0)) (@INSERT nat (S y0) (dotdot x0 y0)) (dotdot x0 y0)).
