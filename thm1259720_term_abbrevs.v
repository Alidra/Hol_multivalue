Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat (Nat.add y0 y1) (Nat.add y2 y3))) (dist (@pair nat nat y1 y3))).
