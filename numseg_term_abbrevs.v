Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : nat => fun y1 : nat => @GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3).
Definition term6 := forall y0 : nat, forall y1 : nat, (dotdot y0 y1) = (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3)).
Definition term5 (x0 : nat) := forall y0 : nat, (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2)).
Definition term2 (x0 : nat) := fun y0 : nat => @GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => @GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2)) x1.
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2))) x1.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dotdot y0 y1) = (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => @GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3)) x0.
Definition term4 (x0 : nat) (x1 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x0 y1) /\ (Peano.le y1 x1)) y1).
