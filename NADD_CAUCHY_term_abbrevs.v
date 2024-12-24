Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 ((fun y0 : nat => dest_nadd x1 y0) x2).
Definition term40 (x0 : nat -> nat) := fun y0 : nat => x0 y0.
Definition term16 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 ((fun y0 : nat => dest_nadd x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => dest_nadd x1 y0) x2)).
Definition term35 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term8 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => dest_nadd x0 y3) y2)) (Nat.mul y2 ((fun y3 : nat => dest_nadd x0 y3) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term0 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term2 := fun y0 : nat -> nat => (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) = (is_nadd y0).
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term50 (x0 : Prop) := forall y0 : nadd, x0.
Definition term37 (x0 : nadd) := @eq Prop (exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2))).
Definition term36 (x0 : nadd) := @eq Prop (exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => dest_nadd x0 y3) y2)) (Nat.mul y2 ((fun y3 : nat => dest_nadd x0 y3) y1)))) (Nat.mul y0 (Nat.add y1 y2))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term48 := forall y0 : nadd, True.
Definition term14 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x0 ((fun y0 : nat => dest_nadd x1 y0) x2)).
Definition term13 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (dest_nadd x1 x2).
Definition term38 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term41 (x0 : nadd) := mk_nadd (fun y0 : nat => dest_nadd x0 y0).
Definition term45 := fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term3 := forall y0 : nat -> nat, (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))).
Definition term7 (x0 : nat -> nat) := (fun y0 : nat -> nat => (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) = (is_nadd y0)) x0.
Definition term21 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2)))).
Definition term28 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term27 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y1 : nat => dest_nadd x0 y1) y0)) (Nat.mul y0 ((fun y1 : nat => dest_nadd x0 y1) x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term32 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term31 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => dest_nadd x0 y2) y1)) (Nat.mul y1 ((fun y2 : nat => dest_nadd x0 y2) y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term42 (x0 : nadd) := mk_nadd (dest_nadd x0).
Definition term47 := forall y0 : nadd, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (dest_nadd y0 y3)) (Nat.mul y3 (dest_nadd y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term17 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2)).
Definition term18 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => dest_nadd x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => dest_nadd x1 y0) x2))).
Definition term11 (x0 : nadd) (x1 : nat) := (fun y0 : nat => dest_nadd x0 y0) x1.
Definition term46 := fun y0 : nadd => True.
Definition term44 (x0 : nadd) := @eq (nat -> nat) (dest_nadd x0).
Definition term26 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 y0)) (Nat.mul y0 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term25 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y1 : nat => dest_nadd x0 y1) y0)) (Nat.mul y0 ((fun y1 : nat => dest_nadd x0 y1) x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term10 (x0 : nadd) := fun y0 : nat => dest_nadd x0 y0.
Definition term4 := forall y0 : nat -> nat, (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) = (is_nadd y0).
Definition term43 (x0 : nadd) := @eq (nat -> nat) (dest_nadd (mk_nadd (fun y0 : nat => dest_nadd x0 y0))).
Definition term39 (x0 : nadd) := dest_nadd (mk_nadd (fun y0 : nat => dest_nadd x0 y0)).
Definition term1 := fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))).
Definition term9 (x0 : nadd) := is_nadd (fun y0 : nat => dest_nadd x0 y0).
Definition term19 (x0 : nat) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (dest_nadd x1 x0)) (Nat.mul x0 (dest_nadd x1 x2))).
Definition term20 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => dest_nadd x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => dest_nadd x1 y0) x2)))).
Definition term30 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (dest_nadd x0 y1)) (Nat.mul y1 (dest_nadd x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term29 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => dest_nadd x0 y2) y1)) (Nat.mul y1 ((fun y2 : nat => dest_nadd x0 y2) y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term15 (x0 : nat) (x1 : nadd) (x2 : nat) := @pair nat nat (Nat.mul x0 (dest_nadd x1 x2)).
Definition term34 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (dest_nadd x0 y2)) (Nat.mul y2 (dest_nadd x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term33 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => dest_nadd x0 y3) y2)) (Nat.mul y2 ((fun y3 : nat => dest_nadd x0 y3) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term24 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (dest_nadd x0 x3)) (Nat.mul x3 (dest_nadd x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term23 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => dest_nadd x0 y0) x3)) (Nat.mul x3 ((fun y0 : nat => dest_nadd x0 y0) x2)))) (Nat.mul x1 (Nat.add x2 x3)).
