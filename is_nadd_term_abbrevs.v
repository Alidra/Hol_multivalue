Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term3 := forall y0 : nat -> nat, (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))).
Definition term4 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term0 := fun y0 : nat -> nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term1 (x0 : nat -> nat) := (fun y0 : nat -> nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
