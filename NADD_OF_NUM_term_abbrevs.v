Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 ((fun y0 : nat => Nat.mul x1 y0) x2).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x2 ((fun y0 : nat => Nat.mul x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.mul x1 y0) x2)).
Definition term49 := fun y0 : nat => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (Nat.mul y0 y3)) (Nat.mul y3 (Nat.mul y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term47 (x0 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul x0 y2)) (Nat.mul y2 (Nat.mul x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term16 (x0 : nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => Nat.mul x0 y3) y2)) (Nat.mul y2 ((fun y3 : nat => Nat.mul x0 y3) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term7 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul x0 (Nat.mul x1 x2)).
Definition term51 := forall y0 : nat, exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (Nat.mul y0 y3)) (Nat.mul y3 (Nat.mul y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term58 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (x0 : nat) := @eq (nat -> nat) (dest_nadd (nadd_of_num x0)).
Definition term1 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x0 ((fun y0 : nat => Nat.mul x1 y0) x2)).
Definition term5 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (NUMERAL 0) (Nat.mul x0 (Nat.add x1 x2)).
Definition term60 := exists y0 : nat, True.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term10 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term21 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term62 (x0 : Prop) := exists y0 : nat, x0.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (Nat.mul x1 x0)) (Nat.mul x0 (Nat.mul x1 x2)))).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (Nat.mul x0 y0)) (Nat.mul y0 (Nat.mul x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y1 : nat => Nat.mul x0 y1) y0)) (Nat.mul y0 ((fun y1 : nat => Nat.mul x0 y1) x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.mul x0 y1)) (Nat.mul y1 (Nat.mul x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term43 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => Nat.mul x0 y2) y1)) (Nat.mul y1 ((fun y2 : nat => Nat.mul x0 y2) y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term6 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term4 (x0 : nat) := dist (@pair nat nat x0 x0).
Definition term18 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term57 := forall y0 : nat, True.
Definition term2 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term56 := fun y0 : nat => True.
Definition term15 (x0 : nat) := is_nadd (fun y0 : nat => Nat.mul x0 y0).
Definition term8 (x0 : nat) := (fun y0 : nat => (nadd_of_num y0) = (mk_nadd (fun y1 : nat => Nat.mul y0 y1))) x0.
Definition term61 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term14 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term9 (x0 : nat) := mk_nadd (fun y0 : nat => Nat.mul x0 y0).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x2 (Nat.mul x1 x0)) (Nat.mul x0 (Nat.mul x1 x2)).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => Nat.mul x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.mul x1 y0) x2))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term22 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (Nat.mul x0 y0)) (Nat.mul y0 (Nat.mul x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y1 : nat => Nat.mul x0 y1) y0)) (Nat.mul y0 ((fun y1 : nat => Nat.mul x0 y1) x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term59 (x0 : Prop) := forall y0 : nat, x0.
Definition term48 := fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term54 := Peano.le (NUMERAL 0).
Definition term13 (x0 : nat) := @eq (nat -> nat) (dest_nadd (mk_nadd (fun y0 : nat => Nat.mul x0 y0))).
Definition term23 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) x1).
Definition term11 (x0 : nat) := dest_nadd (mk_nadd (fun y0 : nat => Nat.mul x0 y0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 y0)) = (NUMERAL 0)) x0.
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x0 (Nat.mul x1 x2)) (Nat.mul x0 (Nat.mul x1 x2))).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x2 (Nat.mul x1 x0)) (Nat.mul x0 (Nat.mul x1 x2))).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => Nat.mul x1 y0) x0)) (Nat.mul x0 ((fun y0 : nat => Nat.mul x1 y0) x2)))).
Definition term42 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.mul x0 y1)) (Nat.mul y1 (Nat.mul x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term41 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => Nat.mul x0 y2) y1)) (Nat.mul y1 ((fun y2 : nat => Nat.mul x0 y2) y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x0 (Nat.mul x1 x2)).
Definition term46 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul x0 y2)) (Nat.mul y2 (Nat.mul x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term45 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => Nat.mul x0 y3) y2)) (Nat.mul y2 ((fun y3 : nat => Nat.mul x0 y3) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term50 := forall y0 : nat, (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (Nat.mul x0 x3)) (Nat.mul x3 (Nat.mul x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 ((fun y0 : nat => Nat.mul x0 y0) x3)) (Nat.mul x3 ((fun y0 : nat => Nat.mul x0 y0) x2)))) (Nat.mul x1 (Nat.add x2 x3)).
