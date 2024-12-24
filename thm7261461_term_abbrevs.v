Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat -> real) := (fun y0 : nat -> real => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (forall y4 : nat, ((Peano.le y2 y4) /\ (Peano.le y4 y3)) -> (y0 y4) = (y1 y4)) -> (@sum nat (dotdot y2 y3) (fun y4 : nat => y0 y4)) = (@sum nat (dotdot y2 y3) y1)) x0.
Definition term1 (x0 : nat -> real) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> (x0 y3) = (y0 y3)) -> (@sum nat (dotdot y1 y2) (fun y3 : nat => x0 y3)) = (@sum nat (dotdot y1 y2) y0).
Definition term6 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) (x3 : nat) := (fun y0 : nat => (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 y0)) -> (x0 y1) = (x2 y1)) -> (@sum nat (dotdot x1 y0) (fun y1 : nat => x0 y1)) = (@sum nat (dotdot x1 y0) x2)) x3.
Definition term3 (x0 : nat -> real) (x1 : nat -> real) := forall y0 : nat, forall y1 : nat, (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> (x0 y2) = (x1 y2)) -> (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 y2)) = (@sum nat (dotdot y0 y1) x1).
Definition term4 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> (x0 y2) = (x1 y2)) -> (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 y2)) = (@sum nat (dotdot y0 y1) x1)) x2.
Definition term2 (x0 : nat -> real) (x1 : nat -> real) := (fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> (x0 y3) = (y0 y3)) -> (@sum nat (dotdot y1 y2) (fun y3 : nat => x0 y3)) = (@sum nat (dotdot y1 y2) y0)) x1.
Definition term5 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) := forall y0 : nat, (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 y0)) -> (x0 y1) = (x2 y1)) -> (@sum nat (dotdot x1 y0) (fun y1 : nat => x0 y1)) = (@sum nat (dotdot x1 y0) x2).
