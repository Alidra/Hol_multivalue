Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := fun y0 : nat => @COND nat (Peano.le x0 y0) y0 x0.
Definition term0 := fun y0 : nat => fun y1 : nat => @COND nat (Peano.le y0 y1) y1 y0.
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.max x0 y0) = (@COND nat (Peano.le x0 y0) y0 x0)) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => @COND nat (Peano.le x0 y0) y0 x0) x1.
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.max x0 y0) = (@COND nat (Peano.le x0 y0) y0 x0).
Definition term6 := forall y0 : nat, forall y1 : nat, (Nat.max y0 y1) = (@COND nat (Peano.le y0 y1) y1 y0).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.max y0 y1) = (@COND nat (Peano.le y0 y1) y1 y0)) x0.
Definition term4 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) x0 x1.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => @COND nat (Peano.le y0 y1) y1 y0) x0.
