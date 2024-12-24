Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat -> real, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (forall y4 : nat, ((Peano.le y2 y4) /\ (Peano.le y4 y3)) -> (y0 y4) = (y1 y4)) -> (@sum nat (dotdot y2 y3) (fun y4 : nat => y0 y4)) = (@sum nat (dotdot y2 y3) y1).
