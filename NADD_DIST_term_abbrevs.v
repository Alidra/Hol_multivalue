Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 x2))) (Nat.mul x1 (dist (@pair nat nat y0 x2)))) x3).
Definition term19 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0)))) x3).
Definition term48 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y2))) (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term13 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (dest_nadd x0 y1))) (Nat.mul y0 y2).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat (Nat.add x2 x1) x2)).
Definition term1 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0)).
Definition term41 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0)) x3.
Definition term43 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term31 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2))).
Definition term45 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x2 x3) -> Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat x2 x3))).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term5 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term3 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term42 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 x3)) (dest_nadd x0 x1))) (Nat.mul x2 x3).
Definition term22 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 x2))) (Nat.mul x1 (dist (@pair nat nat y0 x2))).
Definition term15 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 (Nat.add x1 x2))).
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.add y0 y1) y0)) = y1) x0.
Definition term9 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term23 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 x2))) (Nat.mul x1 (dist (@pair nat nat y0 x2)))) x3.
Definition term16 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0)))) x3.
Definition term7 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term21 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat x2 x3)))).
Definition term47 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 y1))) (Nat.mul x1 (dist (@pair nat nat y0 y1))).
Definition term14 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y0 y1)) (dest_nadd x0 y0))) (Nat.mul x1 y1).
Definition term39 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y0 y1)) (dest_nadd x0 y0))) (Nat.mul x1 y1)) x2.
Definition term29 (x0 : nadd) (x1 : nat) (x2 : nat) := dest_nadd x0 (Nat.add x1 x2).
Definition term40 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x1 y0)) (dest_nadd x0 x1))) (Nat.mul x2 y0).
Definition term44 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x3 x2) -> Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat x2 x3))).
Definition term28 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x1 (Nat.add x2 x0)) (dest_nadd x1 x2)).
Definition term32 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 (Nat.add x0 x1)).
Definition term46 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0))).
Definition term11 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term30 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 (Nat.add x1 x2)))).
Definition term33 (x0 : nat) (x1 : nat) := dist (@pair nat nat (Nat.add x1 x0) x1).
Definition term51 := forall y0 : nadd, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y2) (dest_nadd y0 y3))) (Nat.mul y1 (dist (@pair nat nat y2 y3))).
Definition term37 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 y1)) = (dist (@pair nat nat y1 y0))) x0.
Definition term24 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 x2))) (Nat.mul x1 (dist (@pair nat nat y0 x2)))) (Nat.add x2 x3).
Definition term17 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0)))) (Nat.add x2 x3).
Definition term27 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 (Nat.add x1 x2))).
Definition term12 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 (Nat.add y2 y3)) (dest_nadd y0 y2))) (Nat.mul y1 y3)) x0.
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0) x1.
Definition term18 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 (Nat.add x2 x3)))) (Nat.mul x1 (dist (@pair nat nat x2 (Nat.add x2 x3)))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0))) x1.
Definition term25 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add x3 x2)) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat (Nat.add x3 x2) x3))).
Definition term20 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat x2 x3))).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term50 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 (Nat.add y1 y2)) (dest_nadd x0 y1))) (Nat.mul y0 y2).
Definition term49 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y2))) (Nat.mul y0 (dist (@pair nat nat y1 y2))).
