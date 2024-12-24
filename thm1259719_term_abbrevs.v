Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))).
Definition term0 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0))).
