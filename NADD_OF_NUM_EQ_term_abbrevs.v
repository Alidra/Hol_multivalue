Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term47 (x0 : nat) (x1 : nat) := @pair nat nat (Nat.mul x0 x1).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul (dist (@pair nat nat x0 x1)) x2) x3.
Definition term36 (x0 : nat) (x1 : nat) := nadd_eq (nadd_of_num x0) (nadd_of_num x1).
Definition term61 (x0 : nat) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul x1 y1))) y0.
Definition term37 (x0 : nat) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) y1) (dest_nadd (nadd_of_num x1) y1))) y0.
Definition term31 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))) = (Nat.mul (dist (@pair nat nat y0 y1)) y2)) x0.
Definition term76 (x0 : nat) (x1 : nat) := ((nadd_eq (nadd_of_num x0) (nadd_of_num x1)) -> x0 = x1) /\ ((x0 = x1) -> nadd_eq (nadd_of_num x0) (nadd_of_num x1)).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (dest_nadd (nadd_of_num x0) x2) (dest_nadd (nadd_of_num x1) x2).
Definition term75 (x0 : nat) (x1 : nat) := (x0 = x1) -> x0 = x1.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (Nat.mul (dist (@pair nat nat x0 x1)) y0) x2.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((dist (@pair nat nat x0 y0)) = (NUMERAL 0)) = (x0 = y0)) x1.
Definition term70 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = x1.
Definition term77 (x0 : nat) := forall y0 : nat, (nadd_eq (nadd_of_num x0) (nadd_of_num y0)) = (x0 = y0).
Definition term15 (x0 : nat) := forall y0 : nat, ((dist (@pair nat nat x0 y0)) = (NUMERAL 0)) = (x0 = y0).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (dist (@pair nat nat x0 x1)) x2).
Definition term17 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) y0) (dest_nadd (nadd_of_num x1) y0))) x2.
Definition term33 (x0 : nat) := forall y0 : nat, (x0 = y0) -> nadd_eq (nadd_of_num x0) (nadd_of_num y0).
Definition term62 (x0 : nat) (x1 : nat) := imp (nadd_eq (nadd_of_num x0) (nadd_of_num x1)).
Definition term3 (x0 : nat) (x1 : nat) := fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))) = (Nat.mul (dist (@pair nat nat x0 x1)) y0).
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))) = (Nat.mul (dist (@pair nat nat x0 y0)) y1)) x1.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2))).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul x0 y0) x1.
Definition term7 (x0 : nat) := fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))) = (Nat.mul (dist (@pair nat nat x0 y0)) y1).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) x2) (dest_nadd (nadd_of_num x1) x2))).
Definition term26 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term43 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))) = (Nat.mul (dist (@pair nat nat x0 x1)) y0)) x2.
Definition term30 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term73 (x0 : Prop) := exists y0 : nat, x0.
Definition term74 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (dest_nadd (nadd_of_num x0) x2) (dest_nadd (nadd_of_num x1) x2)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term35 (x0 : nat) (x1 : nat) := (x0 = x1) -> nadd_eq (nadd_of_num x0) (nadd_of_num x1).
Definition term78 := forall y0 : nat, forall y1 : nat, (nadd_eq (nadd_of_num y0) (nadd_of_num y1)) = (y0 = y1).
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))) = (Nat.mul (dist (@pair nat nat y0 y1)) y2).
Definition term12 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (dist (@pair nat nat y0 y1)) y2) = (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))) = (Nat.mul (dist (@pair nat nat x0 y0)) y1).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (dist (@pair nat nat x0 y0)) y1) = (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 y0) x1.
Definition term2 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (dist (@pair nat nat x0 x1)) y0) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))).
Definition term41 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term19 (x0 : nat) := forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul x0 y1) y0) = (x0 = (NUMERAL 0)).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) y0) (dest_nadd (nadd_of_num x1) y0))) x2.
Definition term38 (x0 : nat) (x1 : nat) := dest_nadd (nadd_of_num x0) x1.
Definition term65 (x0 : nat) (x1 : nat) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul x1 y1))) y0) -> x0 = x1.
Definition term72 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term27 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term25 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (Nat.mul (dist (@pair nat nat x0 x1)) y0) x2.
Definition term60 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul x1 y1))) y0.
Definition term59 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) y1) (dest_nadd (nadd_of_num x1) y1))) y0.
Definition term64 (x0 : nat) (x1 : nat) := (nadd_eq (nadd_of_num x0) (nadd_of_num x1)) -> x0 = x1.
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (dist (@pair nat nat x0 x1)) y0) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := @pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) -> nadd_eq (nadd_of_num y0) (nadd_of_num y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.le (Nat.mul y0 y2) y1) = (y0 = (NUMERAL 0))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((dist (@pair nat nat y0 y1)) = (NUMERAL 0)) = (y0 = y1)) x0.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) -> nadd_eq (nadd_of_num x0) (nadd_of_num y0)) x1.
Definition term44 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1).
Definition term46 (x0 : nat) (x1 : nat) := @pair nat nat (dest_nadd (nadd_of_num x0) x1).
Definition term63 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul x1 y1))) y0).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2))) x3.
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_of_num x0) x2) (dest_nadd (nadd_of_num x1) x2))) x3.
Definition term71 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = x1.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))) = (Nat.mul (dist (@pair nat nat x0 x1)) y0).
Definition term29 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term6 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (dist (@pair nat nat x0 y0)) y1) = (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (dist (@pair nat nat x0 x1)) x2.
Definition term45 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.mul x0 y0) x1).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, Peano.le (Nat.mul x0 y1) y0) = (x0 = (NUMERAL 0))) x1.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.mul x0 y1) y0) x1.
Definition term11 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))) = (Nat.mul (dist (@pair nat nat y0 y1)) y2).
Definition term10 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (dist (@pair nat nat y0 y1)) y2) = (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))).
