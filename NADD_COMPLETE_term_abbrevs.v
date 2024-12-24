Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term654 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term221 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq x1 x0) /\ (nadd_eq x0 x2)) -> nadd_eq x1 x2.
Definition term388 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (x1 y0)) (nadd_mul (nadd_of_num y0) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x1 y0))) x2.
Definition term366 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0)) x2.
Definition term833 (x0 : nadd) (x1 : nat -> nat) := forall y0 : nat, nadd_le (nadd_mul (nadd_of_num y0) x0) (nadd_add (nadd_mul (nadd_of_num y0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term849 (x0 : nat -> nat) (x1 : nat) := dest_nadd (nadd_of_num (x0 x1)).
Definition term863 (x0 : nat) := @eq nat ((fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0) x0).
Definition term710 (x0 : nat) := @eq nat ((fun y0 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) x0).
Definition term661 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term230 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1) x0.
Definition term193 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) x0.
Definition term170 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) x0.
Definition term151 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) x0.
Definition term64 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1) x0.
Definition term29 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1) x0.
Definition term790 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le ((fun y0 : nat => Nat.mul (x1 x0) y0) x2) (Nat.add ((fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) y0) x2) x3).
Definition term513 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.mul x0 (S (x1 x2)))).
Definition term689 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (x1 x2).
Definition term75 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term877 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)) x3).
Definition term181 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 y0)) x3.
Definition term290 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) x2).
Definition term773 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) x3.
Definition term481 (x0 : nat) (x1 : nat) := nadd_eq (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) (nadd_mul (nadd_of_num x0) (nadd_of_num x1)).
Definition term247 (x0 : nat) (x1 : nadd) := nadd_mul (nadd_of_num x0) x1.
Definition term894 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := and (nadd_le (nadd_of_num (x0 x1)) (nadd_mul (nadd_of_num x1) x2)).
Definition term185 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term592 (x0 : nat -> nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0).
Definition term128 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term837 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) := (x0 x1) -> nadd_le x1 (mk_nadd x2).
Definition term453 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_eq (nadd_of_num (Nat.mul x0 (x1 x2))) (nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2))).
Definition term342 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nadd) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 x2) -> nadd_le x1 x2.
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (forall y0 : nat, nadd_le (nadd_mul (nadd_of_num y0) x1) (nadd_add (nadd_mul (nadd_of_num y0) x2) x0)) -> nadd_le x1 x2.
Definition term147 (x0 : nat) := forall y0 : nat, nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num y0)) (nadd_of_num (Nat.mul x0 y0)).
Definition term441 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_of_num (x0 x1)) (nadd_mul (nadd_of_num x1) x2).
Definition term811 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.mul (x1 x0) x2) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)).
Definition term111 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term567 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) x2).
Definition term674 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.mul (S (x0 x1)) x2.
Definition term808 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (Nat.mul (x1 x0) y2) (Nat.add (Nat.add (Nat.mul x0 (x1 y2)) y2) y0).
Definition term807 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le ((fun y3 : nat => Nat.mul (x1 x0) y3) y2) (Nat.add ((fun y3 : nat => Nat.add (Nat.mul x0 (x1 y3)) y3) y2) y0).
Definition term398 (x0 : nat -> nat) (x1 : nat) := Peano.le (S (x0 x1)) (x0 x1).
Definition term885 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)) (NUMERAL 0).
Definition term841 (x0 : nat) (x1 : nadd) := nadd_add (nadd_mul (nadd_of_num x0) x1) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term903 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0))))).
Definition term830 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) := exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term501 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3))))).
Definition term486 (x0 : nat) (x1 : nat) (x2 : nadd) := exists y0 : nadd, (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term484 (x0 : nat) (x1 : nat) (x2 : nadd) := exists y0 : nadd, (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term460 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := exists y0 : nadd, (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3))).
Definition term640 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x1 (x0 x2)) x1) (Nat.add (Nat.add (Nat.mul x1 (x0 x2)) x1) x2).
Definition term153 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) -> nadd_le x0 y0) x1.
Definition term584 (x0 : nat -> nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0).
Definition term562 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0) /\ ((fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0).
Definition term884 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.add (Nat.mul (x0 x1) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) y0).
Definition term843 (x0 : nat -> nat) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y1) (Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) y1) y0).
Definition term827 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) (NUMERAL 0)).
Definition term806 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) x2).
Definition term805 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le ((fun y2 : nat => Nat.mul (x1 x0) y2) y1) (Nat.add ((fun y2 : nat => Nat.add (Nat.mul x0 (x1 y2)) y2) y1) x2).
Definition term780 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => Nat.mul (x1 x0) y2) y1) (Nat.add ((fun y2 : nat => Nat.add (Nat.mul x0 (x1 y2)) y2) y1) y0).
Definition term779 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) y0).
Definition term772 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) y1)).
Definition term765 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add y0 (Nat.mul x0 (x1 y1))) y1).
Definition term749 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.add (Nat.mul (x1 x0) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term738 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (S (x1 x0)) y1) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term732 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (S (x1 x0)) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term666 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (S (x1 x0))) y1) (Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) y1) y0).
Definition term664 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term536 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.mul y0 (Nat.add y1 y2)))) /\ (Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.mul y0 (Nat.add y1 y2)))).
Definition term315 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0.
Definition term314 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0.
Definition term144 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term86 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, forall y1 : nat, Peano.le (x0 y1) (Nat.add (x1 y1) y0).
Definition term246 (x0 : nat) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) \/ (nadd_le y1 y0)) (nadd_mul (nadd_of_num x0) x1).
Definition term374 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x2) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x2) y2))) -> Peano.le y1 y0)) (x1 x2).
Definition term568 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0))) x2.
Definition term566 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) x2.
Definition term412 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := exists y0 : nadd, (fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0.
Definition term552 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 y0)))) /\ (Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 y0)))).
Definition term489 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term826 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (Nat.mul (x1 x0) y0) (Nat.add (Nat.add (Nat.mul x0 (x1 y0)) y0) (NUMERAL 0)).
Definition term41 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term296 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) -> Peano.le y0 x2.
Definition term578 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0.
Definition term573 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0.
Definition term784 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.mul (x0 x1) y0) x2.
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nat, nadd_le (nadd_mul (nadd_of_num y0) x0) (nadd_add (nadd_mul (nadd_of_num y0) x1) x2).
Definition term814 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term136 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (dist (@pair nat nat y0 y1)) y2) = ((Peano.le y0 (Nat.add y1 y2)) /\ (Peano.le y1 (Nat.add y0 y2)))) x0.
Definition term119 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term114 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term108 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1)) x0.
Definition term105 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term67 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term754 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))).
Definition term333 (x0 : nadd) (x1 : nat) (x2 : nat) := True /\ (nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_of_num (Nat.mul x1 x2))).
Definition term203 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul (nadd_mul x0 x1) y0) (nadd_mul x0 (nadd_mul x1 y0)).
Definition term286 (x0 : nadd -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) /\ (exists y0 : nat, forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0).
Definition term521 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num (x1 x2)) (nadd_mul (nadd_of_num x2) y0)).
Definition term408 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0)).
Definition term323 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num (NUMERAL 0)) (nadd_mul (nadd_of_num x1) y0)).
Definition term277 := forall y0 : nat -> Prop, ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)).
Definition term506 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))).
Definition term643 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x2 (x0 x1)) y0) /\ (Peano.le y0 (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2))).
Definition term459 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_of_num (x0 x2)))) /\ (nadd_le (nadd_mul (nadd_of_num x1) (nadd_of_num (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3))).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term311 (x0 : nadd -> Prop) (x1 : nat) := and (exists y0 : nat, exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))).
Definition term273 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term20 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_le x1 x0) /\ (nadd_le x0 x2)) -> nadd_le x1 x2.
Definition term844 (x0 : nat -> nat) (x1 : nat) := nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term456 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (nadd_le (nadd_of_num (x0 x2)) (nadd_mul (nadd_of_num x2) x3)) -> nadd_le (nadd_mul (nadd_of_num x1) (nadd_of_num (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term402 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))).
Definition term373 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)) x2 (x1 x2).
Definition term5 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0)) x2.
Definition term818 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term391 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (x1 y0)) (nadd_mul (nadd_of_num y0) y1)).
Definition term361 (x0 : nadd -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y2) y4))) /\ (forall y4 : nat, (exists y5 : nadd, (x0 y5) /\ (nadd_le (nadd_of_num y4) (nadd_mul (nadd_of_num y2) y5))) -> Peano.le y4 y3)) y0 y1.
Definition term359 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term284 (x0 : nadd -> Prop) := forall y0 : nat, exists y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1).
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0)) -> nadd_le x0 x1) x2.
Definition term201 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq (nadd_mul (nadd_mul x0 x1) y0) (nadd_mul x0 (nadd_mul x1 y0)).
Definition term570 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0) /\ ((fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0).
Definition term126 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term714 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) x2.
Definition term912 (x0 : nadd -> Prop) (x1 : nat -> nat) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 (mk_nadd x1)) /\ (forall y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) -> nadd_le (mk_nadd x1) y0).
Definition term824 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x2 (x1 x0)) y0) /\ (Peano.le y0 (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0))).
Definition term356 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) y0))) -> Peano.le x1 (Nat.mul x2 x3).
Definition term915 (x0 : nadd -> Prop) := fun y0 : nadd => forall y1 : nadd, (x0 y1) -> nadd_le y1 y0.
Definition term204 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_mul y0 y1)) (nadd_mul (nadd_mul x0 y0) y1).
Definition term678 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (dest_nadd (nadd_of_num (S (x0 x1))) x2).
Definition term855 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd (nadd_of_num (x0 x1)) x2).
Definition term425 (x0 : nat -> nat) (x1 : nadd -> Prop) := (forall y0 : nat, exists y1 : nadd, (x1 y1) /\ (nadd_le (nadd_of_num (x0 y0)) (nadd_mul (nadd_of_num y0) y1))) -> exists y0 : nadd, (forall y1 : nadd, (x1 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x1 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term386 (x0 : nadd -> Prop) := (forall y0 : nat, exists y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)) -> exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term414 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := @eq Prop (~ (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0)))).
Definition term413 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := @eq Prop (~ (exists y0 : nadd, (fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0)).
Definition term743 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2).
Definition term889 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul (x0 x1) y0) y0).
Definition term736 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, Peano.le (Nat.mul (S (x2 x1)) y0) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term80 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term7 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term160 (x0 : nat) := fun y0 : nat => (Nat.add x0 (Nat.mul x0 y0)) = (Nat.mul x0 (S y0)).
Definition term694 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => Nat.mul x0 (x1 y0).
Definition term626 (x0 : nat -> nat) := (fun y0 : Prop => y0 = (forall y1 : nat, forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y2 y1)))) ((forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0)))).
Definition term435 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := (x0 x1) -> nadd_le (nadd_mul (nadd_of_num x3) x1) (nadd_of_num (S (x2 x3))).
Definition term775 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (x1 x0) x2) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) x3).
Definition term194 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (nadd_eq y0 x0).
Definition term517 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3)).
Definition term879 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) x2).
Definition term898 (x0 : nadd) (x1 : nat) (x2 : nadd) := (nadd_le x0 x2) -> nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) x2).
Definition term457 (x0 : nat -> nat) (x1 : nat) := nadd_of_num (x0 x1).
Definition term785 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le ((fun y0 : nat => Nat.mul (x0 x1) y0) x2).
Definition term495 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nadd, forall y1 : nat, (x0 y0) -> nadd_le (nadd_mul (nadd_of_num y1) y0) (nadd_of_num (S (x1 y1))).
Definition term228 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term217 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1.
Definition term215 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2.
Definition term211 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul (nadd_mul y0 y1) y2) (nadd_mul y0 (nadd_mul y1 y2)).
Definition term210 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_mul y1 y2)) (nadd_mul (nadd_mul y0 y1) y2).
Definition term207 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul (nadd_mul x0 y0) y1) (nadd_mul x0 (nadd_mul y0 y1)).
Definition term206 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_mul y0 y1)) (nadd_mul (nadd_mul x0 y0) y1).
Definition term188 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3).
Definition term187 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y1) /\ (nadd_eq y0 y2)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul y1 y2).
Definition term186 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq x1 y1)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul y0 y1).
Definition term178 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x1 y1).
Definition term176 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_mul x0 y1) (nadd_mul y0 y2).
Definition term174 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3).
Definition term150 := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1.
Definition term62 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1.
Definition term51 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (forall y2 : nat, nadd_le (nadd_mul (nadd_of_num y2) x0) (nadd_add (nadd_mul (nadd_of_num y2) y0) y1)) -> nadd_le x0 y0.
Definition term49 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1.
Definition term32 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) = (nadd_le x0 y0).
Definition term27 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1.
Definition term16 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_le x0 y0) /\ (nadd_le y0 y1)) -> nadd_le x0 y1.
Definition term14 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2.
Definition term10 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y2) -> nadd_le (nadd_mul y1 y0) (nadd_mul y1 y2).
Definition term9 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le x0 y1) -> nadd_le (nadd_mul y0 x0) (nadd_mul y0 y1).
Definition term2 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term0 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term161 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term693 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) (x1 x2)).
Definition term914 (x0 : nat -> nat) (x1 : nadd -> Prop) := (forall y0 : nat, forall y1 : nat, (exists y2 : nadd, (x1 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x0 y0)) -> (forall y0 : nat, exists y1 : nadd, (x1 y1) /\ (nadd_le (nadd_of_num (x0 y0)) (nadd_mul (nadd_of_num y0) y1))) -> exists y0 : nadd, (forall y1 : nadd, (x1 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x1 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term427 (x0 : nat -> nat) (x1 : nadd -> Prop) := (forall y0 : nat, forall y1 : nadd, ~ ((x1 y1) /\ (nadd_le (nadd_of_num (S (x0 y0))) (nadd_mul (nadd_of_num y0) y1)))) -> (forall y0 : nat, exists y1 : nadd, (x1 y1) /\ (nadd_le (nadd_of_num (x0 y0)) (nadd_mul (nadd_of_num y0) y1))) -> exists y0 : nadd, (forall y1 : nadd, (x1 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x1 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term585 (x0 : nat -> nat) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0).
Definition term563 (x0 : nat -> nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0).
Definition term357 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) -> Peano.le y0 (Nat.mul x1 x2).
Definition term625 (x0 : nat -> nat) := (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))).
Definition term623 (x0 : nat -> nat) := (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))).
Definition term603 (x0 : nat -> nat) := (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term768 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.mul (x2 x1) x3) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 x3)) x3)).
Definition term202 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 (nadd_mul x1 y0)) (nadd_mul (nadd_mul x0 x1) y0).
Definition term766 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add x0 (Nat.add (Nat.mul x1 (x2 x3)) x3).
Definition term904 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0))))).
Definition term502 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3))))).
Definition term686 (x0 : nat -> nat) (x1 : nat) := dest_nadd (mk_nadd x0) x1.
Definition term845 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)) x2).
Definition term747 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, Peano.le (Nat.add (Nat.mul (x2 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term350 (x0 : nadd) (x1 : nat) (x2 : nat) := (nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) (nadd_of_num x2))) /\ (nadd_le (nadd_mul (nadd_of_num x1) (nadd_of_num x2)) (nadd_of_num (Nat.mul x1 x2))).
Definition term742 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add (x0 x1) (NUMERAL (BIT1 0))) x2.
Definition term880 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y0) (Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) y0) x2).
Definition term777 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul (x1 x0) y0) (Nat.add (Nat.add (Nat.mul x0 (x1 y0)) y0) x2).
Definition term729 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul (S (x1 x0)) y0) (Nat.add (Nat.add (Nat.mul x0 (x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x2).
Definition term728 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd (nadd_of_num (S (x1 x0))) y0) (Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) y0) x2).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x2) (Nat.add x1 x2).
Definition term608 (x0 : nat -> nat) := fun y0 : nat => fun y1 : nat => Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1)).
Definition term795 (x0 : nat) (x1 : nat -> nat) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) y0)).
Definition term794 (x0 : nat) (x1 : nat -> nat) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le ((fun y2 : nat => Nat.mul (x1 x0) y2) y1) (Nat.add ((fun y2 : nat => Nat.add (Nat.mul x0 (x1 y2)) y2) y1) y0)).
Definition term503 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3)))).
Definition term499 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := nadd_le (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x3) x0)) (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3)))).
Definition term417 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := fun y0 : nadd => ~ ((fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0).
Definition term817 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term238 (x0 : nat) := forall y0 : nat, (nadd_le (nadd_of_num x0) (nadd_of_num y0)) = (Peano.le x0 y0).
Definition term871 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) x2).
Definition term719 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x2).
Definition term700 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 (x1 y0)) x2).
Definition term537 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT1 0)) (Nat.add x0 x1).
Definition term679 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (S (x0 x1)) x2).
Definition term579 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0.
Definition term574 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0)))) x2.
Definition term346 (x0 : nadd) (x1 : nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) (nadd_of_num x2)).
Definition term465 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2))).
Definition term236 (x0 : nat) := fun y0 : nat => (nadd_le (nadd_of_num x0) (nadd_of_num y0)) = (Peano.le x0 y0).
Definition term183 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term746 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => Peano.le (Nat.add (Nat.mul (x2 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term152 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) -> nadd_le x0 y0.
Definition term500 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x3) x0))) /\ (nadd_le (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x3) x0)) (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3))))).
Definition term908 (x0 : nat -> nat) (x1 : nadd) := fun y0 : nadd => forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0).
Definition term835 (x0 : nadd) (x1 : nat -> nat) := fun y0 : nadd => forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) (mk_nadd x1)) y0).
Definition term59 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0).
Definition term610 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))) x1 x2.
Definition term365 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)) x1 x2.
Definition term285 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) /\ (forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0).
Definition term74 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term276 := fun y0 : nat -> Prop => (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)).
Definition term762 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => Peano.le (Nat.mul (x2 x1) y0) (Nat.add (Nat.add x0 (Nat.mul x1 (x2 y0))) y0).
Definition term812 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.mul x2 (x1 x0)) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)).
Definition term783 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) y0.
Definition term483 (x0 : nat) (x1 : nat) (x2 : nadd) := (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) (nadd_mul (nadd_of_num x0) (nadd_of_num x1))) /\ (nadd_eq x2 x2).
Definition term547 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2).
Definition term560 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term443 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2)).
Definition term647 (x0 : nat) (x1 : nat -> nat) := nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term343 (x0 : nadd -> Prop) (x1 : nadd) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 x1) -> forall y0 : nadd, (x0 y0) -> nadd_le y0 x1.
Definition term683 := nadd_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term873 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)).
Definition term548 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2))).
Definition term667 (x0 : nat -> nat) (x1 : nat) := dest_nadd (nadd_of_num (S (x0 x1))).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nadd, (nadd_le (nadd_of_num x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2)))) -> nadd_le (nadd_of_num x0) (nadd_of_num (Nat.mul x1 x2)).
Definition term78 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term905 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term618 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0 x1.
Definition term769 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => Peano.le (Nat.mul (x2 x1) y0) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) y0)).
Definition term819 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term582 (x0 : nat -> nat) := fun y0 : nat => (forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term628 (x0 : nat -> nat) := @eq Prop (((forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0)))) = (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0)))).
Definition term791 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => Peano.le ((fun y1 : nat => Nat.mul (x1 x0) y1) y0) (Nat.add ((fun y1 : nat => Nat.add (Nat.mul x0 (x1 y1)) y1) y0) x2).
Definition term47 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term364 (x0 : nadd -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)) x1.
Definition term670 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.mul (S (x0 x1)) y0) x2.
Definition term901 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) (x4 : nadd) := ((x0 x1) /\ (nadd_le (nadd_of_num (x2 x3)) (nadd_mul (nadd_of_num x3) x1))) -> nadd_le (nadd_of_num (x2 x3)) (nadd_mul (nadd_of_num x3) x4).
Definition term329 (x0 : nat) (x1 : nat) := nadd_of_num (Nat.mul x0 x1).
Definition term334 (x0 : nadd) (x1 : nat) (x2 : nat) := (exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2)))) -> nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_of_num (Nat.mul x1 x2)).
Definition term637 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x1 (x0 x2)) x1) x2.
Definition term129 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term842 (x0 : nat -> nat) (x1 : nat) := nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term796 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term480 (x0 : nat) (x1 : nat) (x2 : nadd) := ((nadd_eq (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) (nadd_mul (nadd_of_num x0) (nadd_of_num x1))) /\ (nadd_eq x2 x2)) -> nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2).
Definition term524 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.mul x2 (x0 x3)) (Nat.add (Nat.mul x3 (x0 x2)) (Nat.mul x1 (Nat.add x2 x3)))) /\ (Peano.le (Nat.mul x3 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x3)) (Nat.mul x1 (Nat.add x2 x3)))).
Definition term461 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := fun y0 : nadd => (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3))).
Definition term19 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_le x1 x0) /\ (nadd_le x0 y0)) -> nadd_le x1 y0) x2.
Definition term321 (x0 : nadd -> Prop) (x1 : nat) (x2 : nadd) := (x0 x2) /\ (nadd_le (nadd_of_num (NUMERAL 0)) (nadd_mul (nadd_of_num x1) x2)).
Definition term389 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x2) y1))) -> Peano.le y0 (x1 x2).
Definition term838 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nadd, (x0 y0) -> nadd_le y0 (mk_nadd x1).
Definition term93 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term872 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) x2).
Definition term720 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) x2).
Definition term701 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)) x2).
Definition term436 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := forall y0 : nadd, (x0 y0) -> nadd_le (nadd_mul (nadd_of_num x2) y0) (nadd_of_num (S (x1 x2))).
Definition term893 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := (exists y0 : nadd, (nadd_le (nadd_of_num (x0 x1)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) x2))) -> nadd_le (nadd_of_num (x0 x1)) (nadd_mul (nadd_of_num x1) x2).
Definition term867 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) x2.
Definition term659 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_add x0 x1).
Definition term854 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul (x0 x1) y0) x2).
Definition term677 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => Nat.mul (S (x0 x1)) y0) x2).
Definition term538 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.mul x0 (x1 x2)).
Definition term231 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0) x1.
Definition term65 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, forall y2 : nat, nadd_le (nadd_mul (nadd_of_num y2) x0) (nadd_add (nadd_mul (nadd_of_num y2) y0) y1)) -> nadd_le x0 y0) x1.
Definition term30 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, (nadd_le x0 y1) /\ (nadd_le y1 y0)) -> nadd_le x0 y0) x1.
Definition term687 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := dest_nadd (nadd_of_num x0) (dest_nadd (mk_nadd x1) x2).
Definition term496 (x0 : nadd -> Prop) (x1 : nat -> nat) := (forall y0 : nat, forall y1 : nadd, (x0 y1) -> nadd_le (nadd_mul (nadd_of_num y0) y1) (nadd_of_num (S (x1 y0)))) -> forall y0 : nadd, forall y1 : nat, (x0 y0) -> nadd_le (nadd_mul (nadd_of_num y1) y0) (nadd_of_num (S (x1 y1))).
Definition term229 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term189 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) -> forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3).
Definition term156 := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) -> forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1.
Definition term63 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1.
Definition term28 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1.
Definition term11 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y2) -> nadd_le (nadd_mul y1 y0) (nadd_mul y1 y2).
Definition term569 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) x2) /\ ((fun y0 : nat => Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0))) x2).
Definition term631 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term906 (x0 : nat -> nat) (x1 : nadd) := forall y0 : nat, nadd_le (nadd_mul (nadd_of_num y0) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num y0) x1) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term727 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul (S (x1 x0)) y0) (Nat.add (Nat.add (Nat.mul x0 (x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x2).
Definition term268 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term248 (x0 : nat) (x1 : nadd) := forall y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x0) x1) y0) \/ (nadd_le y0 (nadd_mul (nadd_of_num x0) x1)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term680 (x0 : nat) (x1 : nat -> nat) := dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term377 (x0 : nadd -> Prop) (x1 : nat -> nat) := fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (x1 y0)) (nadd_mul (nadd_of_num y0) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x1 y0)).
Definition term303 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0).
Definition term897 (x0 : nadd) (x1 : nat) (x2 : nadd) := True /\ (nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term913 (x0 : nadd -> Prop) := fun y0 : nadd => (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term310 (x0 : nadd -> Prop) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0).
Definition term271 (x0 : nadd) := exists y0 : nat, nadd_le x0 (nadd_of_num y0).
Definition term376 (x0 : nadd -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) /\ (forall y3 : nat, (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y1) y4))) -> Peano.le y3 y2)) y0 (x1 y0).
Definition term253 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term520 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nadd => (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2))).
Definition term516 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3))).
Definition term354 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nadd => (nadd_le (nadd_of_num x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2))).
Definition term352 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2))).
Definition term21 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) /\ (nadd_le x1 x2).
Definition term418 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := fun y0 : nadd => ~ ((x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))).
Definition term594 (x0 : nat -> nat) := @eq Prop (forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1)))).
Definition term593 (x0 : nat -> nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0)).
Definition term572 (x0 : nat -> nat) (x1 : nat) := @eq Prop (forall y0 : nat, (Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) /\ (Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0)))).
Definition term571 (x0 : nat -> nat) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0) /\ ((fun y1 : nat => Peano.le (Nat.mul y1 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y1)) (Nat.add x1 y1))) y0)).
Definition term740 (x0 : nat -> nat) (x1 : nat) := Nat.mul (S (x0 x1)).
Definition term705 (x0 : nat) := dest_nadd (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term95 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term382 (x0 : nadd -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num (y0 y1)) (nadd_mul (nadd_of_num y1) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) -> Peano.le y2 (y0 y1)).
Definition term362 (x0 : nadd -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y2) y4))) /\ (forall y4 : nat, (exists y5 : nadd, (x0 y5) /\ (nadd_le (nadd_of_num y4) (nadd_mul (nadd_of_num y2) y5))) -> Peano.le y4 y3)) y1 (y0 y1).
Definition term360 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term890 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) (NUMERAL 0)).
Definition term439 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (x1 y0)) (nadd_mul (nadd_of_num y0) y1))) x2.
Definition term288 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) x2.
Definition term463 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3)))) -> nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3)).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term739 (x0 : nat -> nat) (x1 : nat) := Nat.add (x0 x1) (NUMERAL (BIT1 0)).
Definition term363 (x0 : nadd -> Prop) := fun y0 : nat => fun y1 : nat => (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1).
Definition term518 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (nadd_le (nadd_of_num (Nat.mul x2 (x1 x3))) (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0))) /\ (nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3))).
Definition term48 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term711 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)) x2) (dest_nadd (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))) x2).
Definition term638 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x2 (x0 x1)) x2).
Definition term846 (x0 : nat -> nat) (x1 : nat) := dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term331 (x0 : nadd) (x1 : nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_of_num (Nat.mul x1 x2)).
Definition term553 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) /\ (Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0))).
Definition term307 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0.
Definition term155 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) -> nadd_le x0 x1.
Definition term57 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1) -> nadd_le x0 x1.
Definition term22 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) -> nadd_le x0 x1.
Definition term145 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term870 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul (x0 x1) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) y0) x2).
Definition term853 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul (x0 x1) y1) y0) x2).
Definition term718 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) x2).
Definition term699 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 (x1 y1)) y0) x2).
Definition term676 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul (S (x0 x1)) y1) y0) x2).
Definition term445 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (x0 x1)) x2.
Definition term227 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0.
Definition term61 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, forall y2 : nat, nadd_le (nadd_mul (nadd_of_num y2) x0) (nadd_add (nadd_mul (nadd_of_num y2) y0) y1)) -> nadd_le x0 y0.
Definition term26 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, (nadd_le x0 y1) /\ (nadd_le y1 y0)) -> nadd_le x0 y0.
Definition term302 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) /\ (forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0).
Definition term237 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) = (nadd_le (nadd_of_num x0) (nadd_of_num y0)).
Definition term658 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1))) x1.
Definition term653 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term442 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) x2).
Definition term881 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) x2).
Definition term751 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (x0 x1) x2) x2.
Definition term816 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term634 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) y0)) x1.
Definition term590 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))) x1.
Definition term588 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) x1.
Definition term138 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1)))) x1.
Definition term121 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term115 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term110 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0)) x1.
Definition term106 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term324 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) (x3 : nadd) := (x0 x3) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term270 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, nadd_le y0 (nadd_of_num y1)) x0.
Definition term646 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) := (exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))))) -> nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term565 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0)).
Definition term789 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.add ((fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) y0) x2) x3.
Definition term394 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x2) y1))) -> Peano.le y0 (x1 x2)) (S (x1 x2)).
Definition term473 (x0 : nat) (x1 : nat) (x2 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)))) -> nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term770 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, Peano.le (Nat.mul (x2 x1) y0) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) y0)).
Definition term690 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)).
Definition term477 (x0 : nat) (x1 : nat) (x2 : nadd) := (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2)) /\ (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term858 (x0 : nat) := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x0.
Definition term467 (x0 : nat) (x1 : nat) (x2 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)))) -> nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term850 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := dest_nadd (nadd_of_num (x0 x1)) x2.
Definition term883 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.add (Nat.mul (x0 x1) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) y0).
Definition term882 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y1) (Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) y1) y0).
Definition term793 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le ((fun y2 : nat => Nat.mul (x1 x0) y2) y1) (Nat.add ((fun y2 : nat => Nat.add (Nat.mul x0 (x1 y2)) y2) y1) y0).
Definition term778 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) y0).
Definition term764 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add y0 (Nat.mul x0 (x1 y1))) y1).
Definition term731 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul (S (x1 x0)) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0).
Definition term730 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd (nadd_of_num (S (x1 x0))) y1) (Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) y1) y0).
Definition term313 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0.
Definition term312 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0.
Definition term240 := fun y0 : nat => forall y1 : nat, (nadd_le (nadd_of_num y0) (nadd_of_num y1)) = (Peano.le y0 y1).
Definition term97 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term468 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_eq (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2).
Definition term184 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term191 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y1) /\ (nadd_eq y0 y2)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul y1 y2)) x1.
Definition term177 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_mul x0 y1) (nadd_mul y0 y2)) x1.
Definition term471 (x0 : nat) (x1 : nat) (x2 : nadd) := (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2)) /\ (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term298 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) -> Peano.le y0 x2.
Definition term157 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term848 := nadd_of_num (NUMERAL (BIT1 0)).
Definition term335 (x0 : nadd) (x1 : nat) (x2 : nat) := (nadd_le x0 (nadd_of_num x2)) -> nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) (nadd_of_num x2)).
Definition term798 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x3) -> Peano.le (Nat.mul (x2 x1) x3) (Nat.add (Nat.add (Nat.mul x1 (x2 x3)) x3) x4).
Definition term917 (x0 : nadd -> Prop) := ((exists y0 : nadd, x0 y0) /\ (exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0)) -> exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term405 (x0 : nadd -> Prop) := forall y0 : nadd, ~ (x0 y0).
Definition term632 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term434 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x2) x0) (nadd_of_num (S (x1 x2))).
Definition term306 (x0 : nadd -> Prop) (x1 : nat) := @eq Prop (exists y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0)).
Definition term305 (x0 : nadd -> Prop) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) /\ (forall y1 : nat, ((fun y2 : nat => exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num x1) y3))) y1) -> Peano.le y1 y0)).
Definition term899 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := exists y0 : nadd, (nadd_le (nadd_of_num (x0 x1)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) x2)).
Definition term485 (x0 : nat) (x1 : nat) (x2 : nadd) := fun y0 : nadd => (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term416 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := ~ ((x0 x3) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) x3))).
Definition term861 := fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT1 0)) y1) y0.
Definition term852 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul (x0 x1) y1) y0.
Definition term708 := fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) y0.
Definition term675 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul (S (x0 x1)) y1) y0.
Definition term139 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (dist (@pair nat nat x1 x0)) y0) = ((Peano.le x1 (Nat.add x0 y0)) /\ (Peano.le x0 (Nat.add x1 y0))).
Definition term46 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term649 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term544 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2)))).
Definition term895 (x0 : nadd) (x1 : nat) (x2 : nadd) := nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_mul (nadd_of_num x1) x2).
Definition term355 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) y0)).
Definition term744 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)).
Definition term611 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) x1 y0.
Definition term367 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) /\ (forall y3 : nat, (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y1) y4))) -> Peano.le y3 y2)) x1 y0.
Definition term721 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 (x1 x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)).
Definition term886 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)) (NUMERAL 0)).
Definition term409 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := (fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))) x3.
Definition term283 (x0 : nadd -> Prop) := exists y0 : nadd, x0 y0.
Definition term866 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) x2.
Definition term691 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term800 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => (Peano.le x0 y0) -> Peano.le (Nat.mul (x2 x1) y0) (Nat.add (Nat.add (Nat.mul x1 (x2 y0)) y0) x3).
Definition term349 (x0 : nat) (x1 : nat) := nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) (nadd_of_num (Nat.mul x0 x1)).
Definition term636 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) x2)).
Definition term836 (x0 : nadd) (x1 : nat -> nat) := nadd_le x0 (mk_nadd x1).
Definition term479 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2).
Definition term118 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term171 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0).
Definition term802 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (Nat.mul (x2 x1) y0) (Nat.add (Nat.add (Nat.mul x1 (x2 y0)) y0) x3).
Definition term801 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le ((fun y1 : nat => Nat.mul (x2 x1) y1) y0) (Nat.add ((fun y1 : nat => Nat.add (Nat.mul x1 (x2 y1)) y1) y0) x3).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term256 (x0 : Prop) (x1 : Prop) := @eq Prop (~ (x0 /\ x1)).
Definition term668 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Nat.mul (S (x0 x1)) y0.
Definition term663 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term620 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => Peano.le (Nat.mul y3 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y3)) (Nat.add y2 y3))) y1 y0.
Definition term799 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := fun y0 : nat => (Peano.le x0 y0) -> Peano.le ((fun y1 : nat => Nat.mul (x2 x1) y1) y0) (Nat.add ((fun y1 : nat => Nat.add (Nat.mul x1 (x2 y1)) y1) y0) x3).
Definition term444 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.mul x0 (x1 x2).
Definition term397 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1))) -> Peano.le (S (x1 y0)) (x1 y0).
Definition term381 (x0 : nadd -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num (y0 y1)) (nadd_mul (nadd_of_num y1) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) -> Peano.le y2 (y0 y1)).
Definition term380 (x0 : nadd -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y2) y4))) /\ (forall y4 : nat, (exists y5 : nadd, (x0 y5) /\ (nadd_le (nadd_of_num y4) (nadd_mul (nadd_of_num y2) y5))) -> Peano.le y4 y3)) y1 (y0 y1).
Definition term85 (x0 : nat -> nat) (x1 : nat -> nat) := (fun y0 : nat -> nat => (exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (y0 y2) y1)) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (x0 y3) (Nat.add (y0 y3) y1))) x1.
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) = (nadd_le x0 x1)) x2.
Definition term615 (x0 : nat -> nat) := @eq Prop (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term614 (x0 : nat -> nat) := @eq Prop (forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => Peano.le (Nat.mul y3 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y3)) (Nat.add y2 y3))) y0 y1).
Definition term372 (x0 : nadd -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)).
Definition term371 (x0 : nadd -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y2) y4))) /\ (forall y4 : nat, (exists y5 : nadd, (x0 y5) /\ (nadd_le (nadd_of_num y4) (nadd_mul (nadd_of_num y2) y5))) -> Peano.le y4 y3)) y0 y1).
Definition term423 (x0 : nadd -> Prop) (x1 : nat -> nat) := imp (forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1))) -> Peano.le (S (x1 y0)) (x1 y0)).
Definition term452 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2)).
Definition term401 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))) -> False.
Definition term577 (x0 : nat -> nat) (x1 : nat) := and (forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))).
Definition term264 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term319 (x0 : nadd -> Prop) (x1 : nadd) := and (x0 x1).
Definition term887 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul (x0 x1) x2) x2).
Definition term117 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0)) x0.
Definition term856 := dest_nadd (nadd_of_num (NUMERAL (BIT1 0))).
Definition term265 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term259 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term488 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term275 := fun y0 : nat -> Prop => ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)).
Definition term6 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x2) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term234 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul x0 (nadd_mul x1 y0)) (nadd_mul (nadd_mul x0 x1) y0)) x2.
Definition term262 (x0 : nat) := (~ (Peano.lt x0 x0)) -> (Peano.lt x0 x0) = False.
Definition term839 (x0 : nat -> nat) (x1 : nadd) := (exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0)) -> nadd_le (mk_nadd x0) x1.
Definition term528 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x2 (x0 y0)) (Nat.mul y0 (x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term671 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term169 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term703 := fun y0 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0.
Definition term232 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_mul y1 y2)) (nadd_mul (nadd_mul y0 y1) y2)) x0.
Definition term216 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) x0.
Definition term212 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul (nadd_mul y0 y1) y2) (nadd_mul y0 (nadd_mul y1 y2))) x0.
Definition term190 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3)) x0.
Definition term175 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) x0.
Definition term50 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (forall y3 : nat, nadd_le (nadd_mul (nadd_of_num y3) y0) (nadd_add (nadd_mul (nadd_of_num y3) y1) y2)) -> nadd_le y0 y1) x0.
Definition term31 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le (nadd_add y0 y2) (nadd_add y1 y2)) = (nadd_le y0 y1)) x0.
Definition term15 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) x0.
Definition term12 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y2) -> nadd_le (nadd_mul y1 y0) (nadd_mul y1 y2)) x0.
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) x0.
Definition term252 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x2) /\ (~ (x1 /\ x2)).
Definition term34 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le (nadd_add x0 y0) (nadd_add x1 y0)) = (nadd_le x0 x1).
Definition term421 (x0 : nadd -> Prop) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nadd, ~ ((x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1))).
Definition term797 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x3) -> Peano.le ((fun y0 : nat => Nat.mul (x2 x1) y0) x3) (Nat.add ((fun y0 : nat => Nat.add (Nat.mul x1 (x2 y0)) y0) x3) x4).
Definition term815 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term622 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0)).
Definition term607 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => Peano.le (Nat.mul y3 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y3)) (Nat.add y2 y3))) y1 y0.
Definition term606 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => Peano.le (Nat.mul y3 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y3)) (Nat.add y2 y3))) y0 y1.
Definition term605 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y1 y0.
Definition term604 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term602 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1)).
Definition term597 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1)).
Definition term559 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term558 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add y0 y1)))).
Definition term533 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.mul x1 (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.mul x1 (Nat.add y0 y1)))).
Definition term532 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (x0 y1)) (Nat.mul y1 (x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term438 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) y0).
Definition term437 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, forall y1 : nadd, (x0 y1) -> nadd_le (nadd_mul (nadd_of_num y0) y1) (nadd_of_num (S (x1 y0))).
Definition term422 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, forall y1 : nadd, ~ ((x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1))).
Definition term392 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x1 y0).
Definition term243 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) = (nadd_le (nadd_of_num y0) (nadd_of_num y1)).
Definition term242 := forall y0 : nat, forall y1 : nat, (nadd_le (nadd_of_num y0) (nadd_of_num y1)) = (Peano.le y0 y1).
Definition term166 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (Nat.mul y0 y1)) = (Nat.mul y0 (S y1)).
Definition term165 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term137 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (dist (@pair nat nat x0 y0)) y1) = ((Peano.le x0 (Nat.add y0 y1)) /\ (Peano.le y0 (Nat.add x0 y1))).
Definition term120 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term109 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term104 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term103 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term100 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term99 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term79 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term68 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term66 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term254 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> False) (x0 /\ x1).
Definition term458 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := nadd_le (nadd_mul (nadd_of_num x1) (nadd_of_num (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term639 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x1 (x0 x2)) x1) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2)).
Definition term763 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, Peano.le (Nat.mul (x2 x1) y0) (Nat.add (Nat.add x0 (Nat.mul x1 (x2 y0))) y0).
Definition term787 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add ((fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) y0) x2).
Definition term745 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul (x2 x1) x3) (Nat.mul (NUMERAL (BIT1 0)) x3)) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 x3)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3))).
Definition term909 (x0 : nat -> nat) (x1 : nadd) := nadd_le (mk_nadd x0) x1.
Definition term482 (x0 : nat) (x1 : nat) := and (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) (nadd_mul (nadd_of_num x0) (nadd_of_num x1))).
Definition term564 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0)).
Definition term143 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term831 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) := fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term209 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul (nadd_mul y0 y1) y2) (nadd_mul y0 (nadd_mul y1 y2)).
Definition term208 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_mul y1 y2)) (nadd_mul (nadd_mul y0 y1) y2).
Definition term891 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul (x0 x1) y0) y0).
Definition term874 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) x2) x3.
Definition term722 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) x2) x3.
Definition term735 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => Peano.le (Nat.mul (S (x2 x1)) y0) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term393 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x1 y0)) x2.
Definition term688 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => Nat.mul x0 y0) (x1 x2).
Definition term130 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term505 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_of_num (Nat.add x0 (Nat.mul x0 (x1 x2))).
Definition term782 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Nat.mul (x0 x1) y0.
Definition term657 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_add x0 y0)) = (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)).
Definition term652 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term672 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term609 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))) x1.
Definition term149 (x0 : nat) (x1 : nat) := nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) (nadd_of_num (Nat.mul x0 x1)).
Definition term821 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 (x1 x2)) x0) (Nat.add (Nat.mul x0 (x1 x2)) x2).
Definition term551 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.add x1 x2))) /\ (Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2))).
Definition term404 (x0 : nadd -> Prop) := ~ (exists y0 : nadd, x0 y0).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term822 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (Peano.le (Nat.mul x2 (x1 x0)) (Nat.add (Nat.mul x0 (x1 x2)) x0)) /\ (Peano.le (Nat.add (Nat.mul x0 (x1 x2)) x0) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0))).
Definition term509 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.mul x0 (S (x1 x2)).
Definition term249 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nadd => (nadd_le (nadd_mul (nadd_of_num x2) x0) y0) \/ (nadd_le y0 (nadd_mul (nadd_of_num x2) x0))) (nadd_of_num (S (x1 x2))).
Definition term723 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 (x1 x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) x3.
Definition term340 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (x0 y0) -> nadd_le y0 x1) x2.
Definition term750 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (x0 x1) x2).
Definition term192 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq x1 y1)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul y0 y1)) x2.
Definition term179 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x1 y1)) x2.
Definition term656 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_add y0 y1)) = (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2))) x0.
Definition term651 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term154 (x0 : nadd) (x1 : nadd) := (nadd_eq x0 x1) -> nadd_le x0 x1.
Definition term42 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term173 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1).
Definition term865 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0).
Definition term449 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := (exists y0 : nadd, (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)))) -> nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term43 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term127 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) /\ (y1 y2)) = ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2))) x0.
Definition term550 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2)))) /\ (Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2)))).
Definition term304 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0).
Definition term539 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2)).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term258 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term911 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) -> nadd_le (mk_nadd x1) y0.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term655 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term261 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term148 (x0 : nat) (x1 : nat) := (fun y0 : nat => nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num y0)) (nadd_of_num (Nat.mul x0 y0))) x1.
Definition term345 (x0 : nadd) (x1 : nat) := fun y0 : nadd => (nadd_le x0 y0) /\ (nadd_le y0 (nadd_of_num x1)).
Definition term396 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))) -> Peano.le (S (x1 x2)) (x1 x2).
Definition term907 (x0 : nat -> nat) (x1 : nadd) := exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0).
Definition term834 (x0 : nadd) (x1 : nat -> nat) := exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) (mk_nadd x1)) y0).
Definition term281 (x0 : nadd -> Prop) := exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0.
Definition term58 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0).
Definition term847 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Nat.add (dest_nadd (nadd_of_num (x0 x1)) y0) (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) y0).
Definition term681 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => Nat.add (dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)) y0) (dest_nadd (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term868 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul (x0 x1) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) y0) x2.
Definition term716 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0) x2.
Definition term697 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 (x1 y1)) y0) x2.
Definition term433 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_of_num (S (x0 x1))) (nadd_mul (nadd_of_num x1) x2).
Definition term810 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0).
Definition term916 (x0 : nadd -> Prop) := fun y0 : nadd => x0 y0.
Definition term387 (x0 : nadd -> Prop) := (exists y0 : nat -> nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num (y0 y1)) (nadd_mul (nadd_of_num y1) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) -> Peano.le y2 (y0 y1))) -> exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term712 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.mul x0 (x1 x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2).
Definition term368 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) /\ (forall y3 : nat, (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y1) y4))) -> Peano.le y3 y2)) x1 y0.
Definition term300 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := ((fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) x2) /\ (forall y0 : nat, ((fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0) -> Peano.le y0 x2).
Definition term282 (x0 : nadd -> Prop) (x1 : nadd) := forall y0 : nadd, (x0 y0) -> nadd_le y0 x1.
Definition term734 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.mul (S (x2 x1)) x3) (Nat.add x0 (Nat.add (Nat.mul x1 (x2 x3)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3))).
Definition term89 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term38 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term337 (x0 : nadd) (x1 : nadd) := and (nadd_le x0 x1).
Definition term561 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term627 (x0 : nat -> nat) := @eq Prop ((fun y0 : Prop => y0 = (forall y1 : nat, forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y2 y1)))) ((forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))) /\ (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))))).
Definition term491 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => forall y1 : nadd, (x0 y1) -> nadd_le (nadd_mul (nadd_of_num y0) y1) (nadd_of_num (S (x1 y0)))) x2.
Definition term755 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) (Nat.add x3 x3).
Definition term403 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0)).
Definition term390 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (x1 x2)) (nadd_mul (nadd_of_num x2) y0)).
Definition term322 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (NUMERAL 0)) (nadd_mul (nadd_of_num x1) y0)).
Definition term289 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) y0)).
Definition term320 (x0 : nat) (x1 : nadd) := nadd_le (nadd_of_num (NUMERAL 0)) (nadd_mul (nadd_of_num x0) x1).
Definition term612 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) x1 y0.
Definition term645 (x0 : nadd) (x1 : nat -> nat) := (exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) (mk_nadd x1)) y0)) -> nadd_le x0 (mk_nadd x1).
Definition term669 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := dest_nadd (nadd_of_num (S (x0 x1))) x2.
Definition term864 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (dest_nadd (nadd_of_num (x0 x1)) x2) (dest_nadd (nadd_of_num (NUMERAL (BIT1 0))) x2).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term348 (x0 : nat) (x1 : nat) := nadd_mul (nadd_of_num x0) (nadd_of_num x1).
Definition term220 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0) x2.
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := nadd_le (nadd_of_num x0) (nadd_of_num (Nat.mul x1 x2)).
Definition term613 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => Peano.le (Nat.mul y3 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y3)) (Nat.add y2 y3))) y0 y1.
Definition term494 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) := forall y0 : nat, (x0 x1) -> nadd_le (nadd_mul (nadd_of_num y0) x1) (nadd_of_num (S (x2 y0))).
Definition term341 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nadd) := (x0 x1) -> nadd_le x1 x2.
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term589 (x0 : nat -> nat) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) x1).
Definition term823 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x2 (x1 x0)) y0) /\ (Peano.le y0 (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0))).
Definition term642 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (Nat.mul x2 (x0 x1)) y0) /\ (Peano.le y0 (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2))).
Definition term786 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) y0) x2.
Definition term45 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term704 := NUMERAL (BIT0 (BIT1 0)).
Definition term70 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term226 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1)) -> nadd_eq x0 x1.
Definition term549 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2)).
Definition term650 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term411 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := fun y0 : nadd => (fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0.
Definition term464 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3)))))) -> nadd_le (nadd_mul (nadd_of_num x3) (nadd_mul (nadd_of_num x1) x0)) (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3)))).
Definition term36 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_add x0 x2) (nadd_add x1 x2).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term295 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x2) (nadd_mul (nadd_of_num x1) y0))) -> Peano.le x2 x3.
Definition term476 (x0 : nat) (x1 : nat) (x2 : nadd) := and (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2)).
Definition term820 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 (x1 x2)) x0) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)).
Definition term648 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term910 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nadd) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 x2) -> nadd_le (mk_nadd x1) x2.
Definition term918 := forall y0 : nadd -> Prop, ((exists y1 : nadd, y0 y1) /\ (exists y1 : nadd, forall y2 : nadd, (y0 y2) -> nadd_le y2 y1)) -> exists y1 : nadd, (forall y2 : nadd, (y0 y2) -> nadd_le y2 y1) /\ (forall y2 : nadd, (forall y3 : nadd, (y0 y3) -> nadd_le y3 y2) -> nadd_le y1 y2).
Definition term224 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
Definition term23 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 x1).
Definition term813 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x2 (x1 x0)) y0) /\ (Peano.le y0 (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)))) -> Peano.le (Nat.mul x2 (x1 x0)) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)).
Definition term591 (x0 : nat -> nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) x1) /\ ((fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))) x1).
Definition term292 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) x2).
Definition term774 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.mul x0 (x1 x2)) x2.
Definition term581 (x0 : nat -> nat) (x1 : nat) := (forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) /\ (forall y0 : nat, Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0))).
Definition term279 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1))) x0.
Definition term24 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 y0) /\ (nadd_le y0 x1).
Definition term440 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := (x0 x3) /\ (nadd_le (nadd_of_num (x1 x2)) (nadd_mul (nadd_of_num x2) x3)).
Definition term410 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := (x0 x3) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) x3)).
Definition term4 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term624 (x0 : nat -> nat) := and (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0))).
Definition term599 (x0 : nat -> nat) := and (forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))).
Definition term498 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => (x0 x1) -> nadd_le (nadd_mul (nadd_of_num y0) x1) (nadd_of_num (S (x2 y0)))) x3.
Definition term696 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => Nat.mul x0 (x1 y0)) x2.
Definition term862 (x0 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT1 0)) y1) y0) x0).
Definition term709 (x0 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) y0) x0).
Definition term395 (x0 : nat -> nat) (x1 : nat) := S (x0 x1).
Definition term527 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (Nat.mul x2 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x2)) (Nat.mul x1 (Nat.add x2 y0)))) /\ (Peano.le (Nat.mul y0 (x0 x2)) (Nat.add (Nat.mul x2 (x0 y0)) (Nat.mul x1 (Nat.add x2 y0)))).
Definition term724 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd (nadd_of_num (S (x1 x0))) x2) (Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) x2) x3).
Definition term432 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := (((nadd_le (nadd_mul (nadd_of_num x3) x1) (nadd_of_num (S (x2 x3)))) \/ (nadd_le (nadd_of_num (S (x2 x3))) (nadd_mul (nadd_of_num x3) x1))) /\ (~ ((x0 x1) /\ (nadd_le (nadd_of_num (S (x2 x3))) (nadd_mul (nadd_of_num x3) x1))))) -> (x0 x1) -> nadd_le (nadd_mul (nadd_of_num x3) x1) (nadd_of_num (S (x2 x3))).
Definition term250 (x0 : nat -> nat) (x1 : nat) := nadd_of_num (S (x0 x1)).
Definition term617 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add y0 x1)).
Definition term299 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) -> Peano.le y0 x2.
Definition term684 (x0 : nat) (x1 : nat -> nat) := dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)).
Definition term280 (x0 : nadd -> Prop) := (exists y0 : nadd, x0 y0) /\ (exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0).
Definition term541 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Peano.le (Nat.mul x0 (x1 x2)).
Definition term196 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x0 (nadd_mul x1 x2)) (nadd_mul (nadd_mul x0 x1) x2).
Definition term733 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add x0 (Nat.add (Nat.mul x1 (x2 x3)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3)).
Definition term600 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0.
Definition term595 (x0 : nat -> nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0.
Definition term407 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := forall y0 : nadd, ~ ((fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0).
Definition term633 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term752 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul (x0 x1) x2) x2).
Definition term385 (x0 : nadd -> Prop) := exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term630 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term263 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term244 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (nadd_le (nadd_of_num y0) (nadd_of_num y1))) x0.
Definition term167 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (Nat.mul y0 y1)) = (Nat.mul y0 (S y1))) x0.
Definition term146 (x0 : nat) := (fun y0 : nat => forall y1 : nat, nadd_eq (nadd_mul (nadd_of_num y0) (nadd_of_num y1)) (nadd_of_num (Nat.mul y0 y1))) x0.
Definition term88 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term81 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term347 (x0 : nat) (x1 : nat) := (nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) (nadd_of_num (Nat.mul x0 x1))) -> nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) (nadd_of_num (Nat.mul x0 x1)).
Definition term462 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nadd) := nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term378 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) /\ (forall y3 : nat, (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y1) y4))) -> Peano.le y3 y2)) y0 (x1 y0).
Definition term336 (x0 : nadd) (x1 : nat) := (exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 (nadd_of_num x1))) -> nadd_le x0 (nadd_of_num x1).
Definition term685 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => dest_nadd (nadd_of_num x0) (dest_nadd (mk_nadd x1) y0).
Definition term182 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term197 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul (nadd_mul x0 x1) x2) (nadd_mul x0 (nadd_mul x1 x2)).
Definition term451 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (nadd_eq (nadd_of_num (Nat.mul x0 (x1 x2))) (nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2)))) -> nadd_le (nadd_of_num (Nat.mul x0 (x1 x2))) (nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2))).
Definition term875 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul (x0 x1) x2) (Nat.mul (NUMERAL (BIT1 0)) x2)) x3.
Definition term514 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) (nadd_mul (nadd_of_num x3) (nadd_of_num (S (x1 x2))))) /\ (nadd_le (nadd_mul (nadd_of_num x3) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3))).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term767 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (x0 x1) x2).
Definition term370 (x0 : nadd -> Prop) := fun y0 : nat => exists y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1).
Definition term278 := forall y0 : nat -> Prop, (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)).
Definition term832 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) := nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term205 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul (nadd_mul x0 y0) y1) (nadd_mul x0 (nadd_mul y0 y1)).
Definition term199 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul x0 (nadd_mul x1 x2).
Definition term545 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.add x1 x2))).
Definition term198 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul (nadd_mul x0 x1) x2.
Definition term759 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.mul (x2 x1) x3) (Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) x3).
Definition term741 (x0 : nat -> nat) (x1 : nat) := Nat.mul (Nat.add (x0 x1) (NUMERAL (BIT1 0))).
Definition term316 (x0 : nadd -> Prop) (x1 : nat) := (exists y0 : nat, exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) /\ (exists y0 : nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) -> Peano.le y1 y0).
Definition term344 (x0 : nadd) (x1 : nat) := exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 (nadd_of_num x1)).
Definition term158 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term260 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term715 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x2.
Definition term878 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y0) (Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) y0) x2).
Definition term776 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul (x1 x0) y0) (Nat.add (Nat.add (Nat.mul x0 (x1 y0)) y0) x2).
Definition term726 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => Peano.le (dest_nadd (nadd_of_num (S (x1 x0))) y0) (Nat.add (dest_nadd (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))) y0) x2).
Definition term84 (x0 : nat -> nat) := forall y0 : nat -> nat, (exists y1 : nat, forall y2 : nat, Peano.le (x0 y2) (Nat.add (y0 y2) y1)) = (exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (x0 y3) (Nat.add (y0 y3) y1)).
Definition term426 (x0 : nat -> nat) (x1 : nadd -> Prop) := (forall y0 : nat, (exists y1 : nadd, (x1 y1) /\ (nadd_le (nadd_of_num (S (x0 y0))) (nadd_mul (nadd_of_num y0) y1))) -> Peano.le (S (x0 y0)) (x0 y0)) -> (forall y0 : nat, exists y1 : nadd, (x1 y1) /\ (nadd_le (nadd_of_num (x0 y0)) (nadd_mul (nadd_of_num y0) y1))) -> exists y0 : nadd, (forall y1 : nadd, (x1 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x1 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term400 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := imp (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))).
Definition term293 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := imp (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) y0))).
Definition term474 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2.
Definition term338 (x0 : nadd) (x1 : nadd) (x2 : nat) := (nadd_le x0 x1) /\ (nadd_le x1 (nadd_of_num x2)).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2).
Definition term122 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term760 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.mul (x0 x1) x2.
Definition term297 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) -> Peano.le y0 x2.
Definition term860 (x0 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT1 0)) y1) y0) x0.
Definition term707 (x0 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) y0) x0.
Definition term519 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := exists y0 : nadd, (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2))).
Definition term515 (x0 : nadd) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x2) (nadd_mul (nadd_of_num x3) x0)) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x3 (x1 x2)) x3))).
Definition term353 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nadd, (nadd_le (nadd_of_num x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2))).
Definition term351 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) x0) y0) /\ (nadd_le y0 (nadd_of_num (Nat.mul x1 x2))).
Definition term251 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := (nadd_le (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (S (x0 x1)))) \/ (nadd_le (nadd_of_num (S (x0 x1))) (nadd_mul (nadd_of_num x1) x2)).
Definition term507 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x2) (nadd_of_num (S (x0 x1)))) (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2)).
Definition term508 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.add x0 (Nat.mul x0 (x1 x2)))).
Definition term219 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0.
Definition term18 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_le x1 x0) /\ (nadd_le x0 y0)) -> nadd_le x1 y0.
Definition term415 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := ~ ((fun y0 : nadd => (x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))) x3).
Definition term756 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) x3) x3.
Definition term223 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> nadd_eq x0 x1.
Definition term266 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term702 := dest_nadd (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term892 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := nadd_le (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term172 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0)) x1.
Definition term180 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 y0).
Definition term291 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := and (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x1) (nadd_mul (nadd_of_num x2) y0))).
Definition term761 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) x3.
Definition term475 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_eq (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term470 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term77 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term430 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := ((nadd_le (nadd_mul (nadd_of_num x2) x3) (nadd_of_num (S (x1 x2)))) \/ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) x3))) /\ (~ ((x0 x3) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) x3)))).
Definition term511 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.mul x0 (S (x1 x2)))).
Definition term902 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := (nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0))))) /\ (nadd_le (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0))))).
Definition term369 (x0 : nadd -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (exists y4 : nadd, (x0 y4) /\ (nadd_le (nadd_of_num y3) (nadd_mul (nadd_of_num y2) y4))) /\ (forall y4 : nat, (exists y5 : nadd, (x0 y5) /\ (nadd_le (nadd_of_num y4) (nadd_mul (nadd_of_num y2) y5))) -> Peano.le y4 y3)) y0 y1.
Definition term233 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_mul y0 y1)) (nadd_mul (nadd_mul x0 y0) y1)) x1.
Definition term218 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1) x1.
Definition term213 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul (nadd_mul x0 y0) y1) (nadd_mul x0 (nadd_mul y0 y1))) x1.
Definition term52 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (forall y2 : nat, nadd_le (nadd_mul (nadd_of_num y2) x0) (nadd_add (nadd_mul (nadd_of_num y2) y0) y1)) -> nadd_le x0 y0) x1.
Definition term33 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le (nadd_add x0 y1) (nadd_add y0 y1)) = (nadd_le x0 y0)) x1.
Definition term17 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_le x0 y0) /\ (nadd_le y0 y1)) -> nadd_le x0 y1) x1.
Definition term13 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le x0 y1) -> nadd_le (nadd_mul y0 x0) (nadd_mul y0 y1)) x1.
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1)) x1.
Definition term598 (x0 : nat -> nat) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0).
Definition term576 (x0 : nat -> nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => Peano.le (Nat.mul x1 (x0 y1)) (Nat.add (Nat.mul y1 (x0 x1)) (Nat.add x1 y1))) y0).
Definition term526 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x2 (x0 y0)) (Nat.mul y0 (x0 x2)))) (Nat.mul x1 (Nat.add x2 y0)).
Definition term857 := fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0.
Definition term469 (x0 : nat) (x1 : nat) (x2 : nadd) := and (nadd_eq (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2)).
Definition term317 (x0 : nadd) := (fun y0 : nadd => nadd_le (nadd_of_num (NUMERAL 0)) y0) x0.
Definition term546 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 (x0 x2)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2)).
Definition term200 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq (nadd_mul x0 (nadd_mul x1 y0)) (nadd_mul (nadd_mul x0 x1) y0).
Definition term497 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nadd) := (fun y0 : nadd => forall y1 : nat, (x0 y0) -> nadd_le (nadd_mul (nadd_of_num y1) y0) (nadd_of_num (S (x1 y1)))) x2.
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.mul x0 y0)) = (Nat.mul x0 (S y0))) x1.
Definition term825 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (Peano.le x0 x2) -> Peano.le (Nat.mul (x1 x0) x2) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2) (NUMERAL 0)).
Definition term665 (x0 : nat) (x1 : nat -> nat) := nadd_le (nadd_of_num (S (x1 x0))) (nadd_add (nadd_mul (nadd_of_num x0) (mk_nadd x1)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term492 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := (fun y0 : nadd => (x0 y0) -> nadd_le (nadd_mul (nadd_of_num x2) y0) (nadd_of_num (S (x1 x2)))) x3.
Definition term239 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (nadd_le (nadd_of_num x0) (nadd_of_num y0)).
Definition term660 (x0 : nadd) (x1 : nadd) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0).
Definition term662 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
Definition term419 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := forall y0 : nadd, ~ ((x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0))).
Definition term455 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_le (nadd_of_num (Nat.mul x0 (x1 x2))) (nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2))).
Definition term888 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.add (Nat.mul (x0 x1) y0) (Nat.mul (NUMERAL (BIT1 0)) y0)) (NUMERAL 0)).
Definition term490 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (nadd_le (nadd_mul (nadd_of_num x3) x0) (nadd_of_num (S (x2 x3)))) -> nadd_le (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x3) x0)) (nadd_mul (nadd_of_num x1) (nadd_of_num (S (x2 x3)))).
Definition term454 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num (x1 x2))) (nadd_of_num (Nat.mul x0 (x1 x2))).
Definition term399 (x0 : nat -> nat) (x1 : nat) := Peano.lt (x0 x1) (x0 x1).
Definition term542 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 x2))).
Definition term525 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term330 (x0 : nat) (x1 : nat) (x2 : nadd) := and (nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term448 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2).
Definition term96 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term446 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (exists y0 : nadd, (nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) y0) /\ (nadd_le y0 (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2)))) -> nadd_le (nadd_of_num (Nat.mul x1 (x0 x2))) (nadd_of_num (Nat.add (Nat.mul x2 (x0 x1)) x2)).
Definition term695 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := dest_nadd (nadd_mul (nadd_of_num x0) (mk_nadd x1)) x2.
Definition term829 (x0 : nadd) (x1 : nat) (x2 : nat -> nat) := (nadd_le (nadd_mul (nadd_of_num x1) x0) (nadd_of_num (S (x2 x1)))) /\ (nadd_le (nadd_of_num (S (x2 x1))) (nadd_add (nadd_mul (nadd_of_num x1) (mk_nadd x2)) (nadd_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term76 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term274 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term713 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => Nat.add (Nat.mul x0 (x1 y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term267 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term308 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num x1) y2))) y0.
Definition term809 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (Nat.mul (x1 x0) y2) (Nat.add (Nat.add (Nat.mul x0 (x1 y2)) y2) y0).
Definition term781 (x0 : nat) (x1 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le ((fun y3 : nat => Nat.mul (x1 x0) y3) y2) (Nat.add ((fun y3 : nat => Nat.add (Nat.mul x0 (x1 y3)) y3) y2) y0).
Definition term309 (x0 : nadd -> Prop) (x1 : nat) := exists y0 : nat, exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1)).
Definition term87 (x0 : nat -> nat) (x1 : nat -> nat) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (x0 y2) (Nat.add (x1 y2) y0).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term583 (x0 : nat -> nat) := forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term379 (x0 : nadd -> Prop) (x1 : nat -> nat) := forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (x1 y0)) (nadd_mul (nadd_of_num y0) y1))) /\ (forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) -> Peano.le y1 (x1 y0)).
Definition term431 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x2 \/ x0) /\ (~ (x1 /\ x0))) -> x1 -> x2.
Definition term83 (x0 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat -> nat, (exists y2 : nat, forall y3 : nat, Peano.le (y0 y3) (Nat.add (y1 y3) y2)) = (exists y2 : nat, exists y3 : nat, forall y4 : nat, (Peano.le y3 y4) -> Peano.le (y0 y4) (Nat.add (y1 y4) y2))) x0.
Definition term543 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 (x0 x2)) (Nat.add (Nat.mul x2 (x0 x1)) (Nat.add x1 x2)).
Definition term478 (x0 : nat) (x1 : nat) (x2 : nadd) := (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) x2)) /\ True.
Definition term195 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (nadd_eq y0 x0)) x1.
Definition term429 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nadd) := (fun y0 : nadd => ~ ((x0 y0) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y0)))) x3.
Definition term725 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (S (x1 x0)) x2) (Nat.add (Nat.add (Nat.mul x0 (x1 x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) x3).
Definition term629 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (Nat.mul x2 (x0 x1)) y0) /\ (Peano.le y0 (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2)))) -> Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2)).
Definition term255 (x0 : Prop) (x1 : Prop) := (x0 /\ x1) -> False.
Definition term375 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num (x1 x2)) (nadd_mul (nadd_of_num x2) y0))) /\ (forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x2) y1))) -> Peano.le y0 (x1 x2)).
Definition term301 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) := (exists y0 : nadd, (x0 y0) /\ (nadd_le (nadd_of_num x2) (nadd_mul (nadd_of_num x1) y0))) /\ (forall y0 : nat, (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) -> Peano.le y0 x2).
Definition term792 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := forall y0 : nat, Peano.le ((fun y1 : nat => Nat.mul (x1 x0) y1) y0) (Nat.add ((fun y1 : nat => Nat.add (Nat.mul x0 (x1 y1)) y1) y0) x2).
Definition term616 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0 x1.
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.mul x1 x2).
Definition term522 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) x1).
Definition term406 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (exists y0 : nadd, (fun y1 : nadd => (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 x2))) (nadd_mul (nadd_of_num x2) y1))) y0).
Definition term287 (x0 : nadd -> Prop) (x1 : nat) := fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1)).
Definition term94 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term641 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x2 (x0 x1)) (Nat.add (Nat.mul x1 (x0 x2)) x1)) /\ (Peano.le (Nat.add (Nat.mul x1 (x0 x2)) x1) (Nat.add (Nat.mul x1 (x0 x2)) (Nat.add x1 x2))).
Definition term447 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_of_num (Nat.mul x0 (x1 x2)).
Definition term53 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0)) -> nadd_le x0 x1.
Definition term788 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 (x1 x2)) x2).
Definition term692 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) (x1 x2)).
Definition term466 (x0 : nat) (x1 : nat) (x2 : nadd) := (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))) -> nadd_le (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2)).
Definition term318 (x0 : nadd) := nadd_le (nadd_of_num (NUMERAL 0)) x0.
Definition term159 (x0 : nat) := fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term235 (x0 : nat) (x1 : nat) := nadd_le (nadd_of_num x0) (nadd_of_num x1).
Definition term619 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add y0 x1)).
Definition term580 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0)).
Definition term575 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0)).
Definition term758 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Peano.le (Nat.add (Nat.mul (x2 x1) x3) x3) (Nat.add (Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) x3) x3).
Definition term869 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul (x0 x1) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) y0.
Definition term717 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) y0.
Definition term472 (x0 : nat) (x1 : nat) (x2 : nadd) := True /\ (nadd_eq (nadd_mul (nadd_mul (nadd_of_num x1) (nadd_of_num x0)) x2) (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term339 (x0 : nadd) (x1 : nadd) := (nadd_le x0 x1) /\ True.
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 (Nat.add x0 x2)) /\ (Peano.le x0 (Nat.add x1 x2)).
Definition term450 (x0 : nat) (x1 : nat) (x2 : nadd) := nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2).
Definition term162 (x0 : nat) := forall y0 : nat, (Nat.add x0 (Nat.mul x0 y0)) = (Nat.mul x0 (S y0)).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1)) x2.
Definition term876 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd (nadd_mul (nadd_of_num x1) (mk_nadd x0)) x2) (Nat.add (dest_nadd (nadd_add (nadd_of_num (x0 x1)) (nadd_of_num (NUMERAL (BIT1 0)))) x2) x3).
Definition term840 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := (exists y0 : nadd, (nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) y0) /\ (nadd_le y0 (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0)))))) -> nadd_le (nadd_mul (nadd_of_num x1) (mk_nadd x0)) (nadd_add (nadd_mul (nadd_of_num x1) x2) (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term601 (x0 : nat -> nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.add y1 y2))) y0.
Definition term596 (x0 : nat -> nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.add y1 y2))) y0.
Definition term269 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term384 (x0 : nadd -> Prop) := imp (exists y0 : nat -> nat, forall y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num (y0 y1)) (nadd_mul (nadd_of_num y1) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y1) y3))) -> Peano.le y2 (y0 y1))).
Definition term428 (x0 : nadd -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => forall y1 : nadd, ~ ((x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1)))) x2.
Definition term60 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, forall y1 : nat, nadd_le (nadd_mul (nadd_of_num y1) x0) (nadd_add (nadd_mul (nadd_of_num y1) x1) y0)) -> nadd_le x0 x1.
Definition term25 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 x1)) -> nadd_le x0 x1.
Definition term424 (x0 : nadd -> Prop) (x1 : nat -> nat) := imp (forall y0 : nat, forall y1 : nadd, ~ ((x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1)))).
Definition term383 (x0 : nadd -> Prop) := imp (forall y0 : nat, exists y1 : nat, (exists y2 : nadd, (x0 y2) /\ (nadd_le (nadd_of_num y1) (nadd_mul (nadd_of_num y0) y2))) /\ (forall y2 : nat, (exists y3 : nadd, (x0 y3) /\ (nadd_le (nadd_of_num y2) (nadd_mul (nadd_of_num y0) y3))) -> Peano.le y2 y1)).
Definition term40 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term859 (x0 : nat) := (fun y0 : nat => Nat.mul (NUMERAL (BIT1 0)) y0) x0.
Definition term706 (x0 : nat) := (fun y0 : nat => Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) x0.
Definition term510 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := nadd_of_num (Nat.mul x0 (S (x1 x2))).
Definition term851 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul (x0 x1) y1) y0) x2.
Definition term673 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul (S (x0 x1)) y1) y0) x2.
Definition term900 (x0 : nat -> nat) (x1 : nat) (x2 : nadd) := fun y0 : nadd => (nadd_le (nadd_of_num (x0 x1)) y0) /\ (nadd_le y0 (nadd_mul (nadd_of_num x1) x2)).
Definition term896 (x0 : nat -> nat) (x1 : nadd) (x2 : nat) (x3 : nadd) := (nadd_le (nadd_of_num (x0 x2)) (nadd_mul (nadd_of_num x2) x1)) /\ (nadd_le (nadd_mul (nadd_of_num x2) x1) (nadd_mul (nadd_of_num x2) x3)).
Definition term294 (x0 : nadd -> Prop) (x1 : nat) (x2 : nat) (x3 : nat) := ((fun y0 : nat => exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num y0) (nadd_mul (nadd_of_num x1) y1))) x2) -> Peano.le x2 x3.
Definition term272 (x0 : nadd) (x1 : nat) := nadd_le x0 (nadd_of_num x1).
Definition term635 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) x1)) x2.
Definition term214 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul (nadd_mul x0 x1) y0) (nadd_mul x0 (nadd_mul x1 y0))) x2.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1))) x1.
Definition term698 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 (x1 y1)) y0.
Definition term487 (x0 : nat) (x1 : nat) (x2 : nadd) := fun y0 : nadd => (nadd_eq (nadd_mul (nadd_of_num x1) (nadd_mul (nadd_of_num x0) x2)) y0) /\ (nadd_eq y0 (nadd_mul (nadd_of_num x0) (nadd_mul (nadd_of_num x1) x2))).
Definition term753 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add (Nat.add x0 (Nat.mul x1 (x2 x3))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3).
Definition term493 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nat -> nat) (x3 : nat) := (forall y0 : nat, forall y1 : nadd, (x0 y1) -> nadd_le (nadd_mul (nadd_of_num y0) y1) (nadd_of_num (S (x2 y0)))) -> nadd_le (nadd_mul (nadd_of_num x3) x1) (nadd_of_num (S (x2 x3))).
Definition term332 (x0 : nat) (x1 : nadd) (x2 : nat) (x3 : nat) := (nadd_le (nadd_of_num x0) (nadd_mul (nadd_of_num x2) x1)) /\ (nadd_le (nadd_mul (nadd_of_num x2) x1) (nadd_of_num (Nat.mul x2 x3))).
Definition term512 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.mul x0 (S (x1 x2))))) -> nadd_le (nadd_mul (nadd_of_num x0) (nadd_of_num (S (x1 x2)))) (nadd_of_num (Nat.mul x0 (S (x1 x2)))).
Definition term682 (x0 : nat) (x1 : nat -> nat) := nadd_mul (nadd_of_num x0) (mk_nadd x1).
Definition term757 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := Nat.add x0 (Nat.mul x1 (x2 x3)).
Definition term358 (x0 : nadd) := fun y0 : nat => nadd_le x0 (nadd_of_num y0).
Definition term828 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) (NUMERAL 0)).
Definition term804 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (Nat.mul (x1 x0) y1) (Nat.add (Nat.add (Nat.mul x0 (x1 y1)) y1) x2).
Definition term803 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le ((fun y2 : nat => Nat.mul (x1 x0) y2) y1) (Nat.add ((fun y2 : nat => Nat.add (Nat.mul x0 (x1 y2)) y2) y1) x2).
Definition term771 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul (x1 x0) y1) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) y1)).
Definition term748 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.add (Nat.mul (x1 x0) y1) (Nat.mul (NUMERAL (BIT1 0)) y1)) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term737 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul (S (x1 x0)) y1) (Nat.add y0 (Nat.add (Nat.mul x0 (x1 y1)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term621 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y1 y0)).
Definition term587 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1)).
Definition term586 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1)).
Definition term557 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.add y0 y1))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.add y0 y1))).
Definition term556 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add y0 y1)))).
Definition term531 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul y0 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y0)) (Nat.mul x1 (Nat.add y0 y1)))) /\ (Peano.le (Nat.mul y1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 y1)) (Nat.mul x1 (Nat.add y0 y1)))).
Definition term530 (x0 : nat -> nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 (x0 y1)) (Nat.mul y1 (x0 y0)))) (Nat.mul x1 (Nat.add y0 y1)).
Definition term241 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (nadd_le (nadd_of_num y0) (nadd_of_num y1)).
Definition term164 := fun y0 : nat => forall y1 : nat, (Nat.add y0 (Nat.mul y0 y1)) = (Nat.mul y0 (S y1)).
Definition term163 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term98 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term644 := NUMERAL (BIT1 0).
Definition term44 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term555 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.add x1 y0))) /\ (Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.add x1 y0))).
Definition term554 (x0 : nat -> nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x1 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x1)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 y0)))) /\ (Peano.le (Nat.mul y0 (x0 x1)) (Nat.add (Nat.mul x1 (x0 y0)) (Nat.mul (NUMERAL (BIT1 0)) (Nat.add x1 y0)))).
Definition term529 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.mul x2 (x0 y0)) (Nat.add (Nat.mul y0 (x0 x2)) (Nat.mul x1 (Nat.add x2 y0)))) /\ (Peano.le (Nat.mul y0 (x0 x2)) (Nat.add (Nat.mul x2 (x0 y0)) (Nat.mul x1 (Nat.add x2 y0)))).
Definition term222 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x1 x2).
Definition term504 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := Nat.add x0 (Nat.mul x0 (x1 x2)).
Definition term535 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y1 (x0 y2)) (Nat.add (Nat.mul y2 (x0 y1)) (Nat.mul y0 (Nat.add y1 y2)))) /\ (Peano.le (Nat.mul y2 (x0 y1)) (Nat.add (Nat.mul y1 (x0 y2)) (Nat.mul y0 (Nat.add y1 y2)))).
Definition term534 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term102 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term101 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term420 (x0 : nadd -> Prop) (x1 : nat -> nat) := fun y0 : nat => (exists y1 : nadd, (x0 y1) /\ (nadd_le (nadd_of_num (S (x1 y0))) (nadd_mul (nadd_of_num y0) y1))) -> Peano.le (S (x1 y0)) (x1 y0).
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term540 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x2 (x0 x1)) (Nat.add x1 x2).
Definition term245 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (nadd_le (nadd_of_num x0) (nadd_of_num y0))) x1.
Definition term225 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
Definition term523 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x2 (x0 x3)) (Nat.mul x3 (x0 x2)))) (Nat.mul x1 (Nat.add x2 x3)).
