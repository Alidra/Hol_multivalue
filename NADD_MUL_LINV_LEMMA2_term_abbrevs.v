Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : nadd) := (exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term7 (x0 : nadd) (x1 : nat) := (forall y0 : nadd, forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1)) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term20 (x0 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term12 (x0 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term0 := forall y0 : nadd, forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1).
Definition term4 (x0 : nadd) (x1 : nat) := (~ ((dest_nadd x0 x1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1)) x0.
Definition term8 := (forall y0 : nadd, forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1)) -> forall y0 : nadd, forall y1 : nat, (~ ((dest_nadd y0 y1) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y1) (nadd_rinv y0 y1)) (Nat.mul y1 y1))) (dest_nadd y0 y1).
Definition term6 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term19 (x0 : nat) (x1 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0).
Definition term3 (x0 : nadd) (x1 : nat) := (fun y0 : nat => (~ ((dest_nadd x0 y0) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y0) (nadd_rinv x0 y0)) (Nat.mul y0 y0))) (dest_nadd x0 y0)) x1.
Definition term16 (x0 : nat) (x1 : nadd) (x2 : nat) := (forall y0 : nat, (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0))) -> ~ ((dest_nadd x1 x2) = (NUMERAL 0)).
Definition term14 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0))) x2.
Definition term9 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> ~ ((dest_nadd y0 y2) = (NUMERAL 0))) x0.
Definition term15 (x0 : nat) (x1 : nadd) (x2 : nat) := (Peano.le x0 x2) -> ~ ((dest_nadd x1 x2) = (NUMERAL 0)).
Definition term13 (x0 : nat) (x1 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0)).
Definition term25 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y2) (nadd_rinv y0 y2)) (Nat.mul y2 y2))) (dest_nadd y0 y2).
Definition term24 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term10 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term18 (x0 : nat) (x1 : nadd) (x2 : nat) := (Peano.le x0 x2) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))) (dest_nadd x1 x2).
Definition term22 (x0 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> ~ ((dest_nadd x0 y1) = (NUMERAL 0)).
Definition term5 (x0 : nadd) (x1 : nat) := ~ ((dest_nadd x0 x1) = (NUMERAL 0)).
Definition term11 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term2 (x0 : nadd) := forall y0 : nat, (~ ((dest_nadd x0 y0) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y0) (nadd_rinv x0 y0)) (Nat.mul y0 y0))) (dest_nadd x0 y0).
Definition term21 (x0 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term17 (x0 : nat) (x1 : nadd) := (forall y0 : nat, (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0))) -> forall y0 : nat, (Peano.le x0 y0) -> ~ ((dest_nadd x1 y0) = (NUMERAL 0)).
