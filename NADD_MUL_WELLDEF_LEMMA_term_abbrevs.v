Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : nadd) (x1 : nadd) := dest_nadd (nadd_mul x0 x1).
Definition term60 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x2 y1))) y0) -> exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x1 (dest_nadd x2 y1)))) y0.
Definition term25 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term9 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x1 (dest_nadd x2 y0)))) (Nat.mul x3 x4).
Definition term47 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3))).
Definition term62 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (exists y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) y0) /\ (Peano.le y0 (Nat.mul x4 x5))) -> Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) (Nat.mul x4 x5).
Definition term39 (x0 : nadd) (x1 : nadd) := fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0.
Definition term58 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x1 (dest_nadd x2 y1)))) y0.
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y1) (dest_nadd (nadd_mul x1 x2) y1))) y0.
Definition term28 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term18 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y2))) (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term63 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term51 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) x4.
Definition term77 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nadd) (x4 : nat) := and (Peano.le (dist (@pair nat nat (dest_nadd x0 (dest_nadd x2 x4)) (dest_nadd x0 (dest_nadd x3 x4)))) (Nat.mul x1 (dist (@pair nat nat (dest_nadd x2 x4) (dest_nadd x3 x4))))).
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term82 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term31 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term93 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y1 y2) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term92 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) (Nat.mul x4 x5).
Definition term41 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2).
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term12 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term70 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2) x3.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd (nadd_mul x0 x1) x2.
Definition term79 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (dest_nadd x1 x3) (dest_nadd x2 x3))) x4).
Definition term40 (x0 : nadd) (x1 : nadd) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2).
Definition term22 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1))) x1.
Definition term65 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term42 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd (nadd_mul x0 x1) x2).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term27 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term74 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0)))) x3.
Definition term50 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x3) (dest_nadd (nadd_mul x1 x2) x3))) x4.
Definition term49 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))).
Definition term59 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x2) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term81 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term64 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term19 (x0 : nadd) (x1 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 y1))) (Nat.mul x1 (dist (@pair nat nat y0 y1))).
Definition term13 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term43 (x0 : nadd) (x1 : nadd) (x2 : nat) := @pair nat nat (dest_nadd x0 (dest_nadd x1 x2)).
Definition term80 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term72 (x0 : nadd) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 y1))) (Nat.mul x1 (dist (@pair nat nat y0 y1)))) x2.
Definition term21 (x0 : nadd) := forall y0 : nadd, (dest_nadd (nadd_mul x0 y0)) = (fun y1 : nat => dest_nadd x0 (dest_nadd y0 y1)).
Definition term36 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term84 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := exists y0 : nat, (Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) y0) /\ (Peano.le y0 (Nat.mul x4 x5)).
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x1 (dest_nadd x2 y0)))) x3.
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y0) (dest_nadd (nadd_mul x1 x2) y0))) x3.
Definition term20 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (dest_nadd (nadd_mul y0 y1)) = (fun y2 : nat => dest_nadd y0 (dest_nadd y1 y2))) x0.
Definition term61 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x3) (dest_nadd (nadd_mul x1 x2) x3)).
Definition term86 (x0 : nat) (x1 : nadd) (x2 : nadd) (x3 : nat) := Nat.mul x0 (dist (@pair nat nat (dest_nadd x1 x3) (dest_nadd x2 x3))).
Definition term24 (x0 : nadd) (x1 : nadd) := fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0).
Definition term66 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => dest_nadd x0 (dest_nadd x1 y1)) y0) x2.
Definition term73 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 y0))) (Nat.mul x1 (dist (@pair nat nat x2 y0))).
Definition term78 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le (Nat.mul x3 (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2)))) (Nat.mul x3 x4).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nat) := (fun y0 : nat => dest_nadd x0 (dest_nadd x1 y0)) x2.
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y0)) (dest_nadd x1 (dest_nadd x2 y0)))) x3.
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y0) (dest_nadd (nadd_mul x1 x2) y0))) x3.
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term90 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term57 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 y1)) (dest_nadd x1 (dest_nadd x2 y1)))) y0.
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) y1) (dest_nadd (nadd_mul x1 x2) y1))) y0.
Definition term91 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term44 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (dest_nadd (nadd_mul x1 x0) x3) (dest_nadd (nadd_mul x1 x2) x3).
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term85 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := fun y0 : nat => (Peano.le (dist (@pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)))) y0) /\ (Peano.le y0 (Nat.mul x4 x5)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term83 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) (x4 : nat) (x5 : nat) := (Peano.le (dist (@pair nat nat (dest_nadd x0 (dest_nadd x1 x3)) (dest_nadd x0 (dest_nadd x2 x3)))) (Nat.mul x4 (dist (@pair nat nat (dest_nadd x1 x3) (dest_nadd x2 x3))))) /\ (Peano.le (Nat.mul x4 (dist (@pair nat nat (dest_nadd x1 x3) (dest_nadd x2 x3)))) (Nat.mul x4 x5)).
Definition term11 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term30 (x0 : nadd) (x1 : nadd) := imp (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0).
Definition term17 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y2) (dest_nadd y0 y3))) (Nat.mul y1 (dist (@pair nat nat y2 y3)))) x0.
Definition term71 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3.
Definition term26 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term76 (x0 : nadd) (x1 : nat) (x2 : nadd) (x3 : nadd) (x4 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 (dest_nadd x2 x4)) (dest_nadd x0 (dest_nadd x3 x4)))) (Nat.mul x1 (dist (@pair nat nat (dest_nadd x2 x4) (dest_nadd x3 x4)))).
Definition term29 (x0 : nadd) (x1 : nadd) := imp (nadd_eq x0 x1).
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nat) := dest_nadd x0 (dest_nadd x1 x2).
Definition term75 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x0 x3))) (Nat.mul x1 (dist (@pair nat nat x2 x3))).
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := @pair nat nat (dest_nadd x1 (dest_nadd x0 x3)) (dest_nadd x1 (dest_nadd x2 x3)).
Definition term48 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd (nadd_mul x1 x0) x3) (dest_nadd (nadd_mul x1 x2) x3))).
Definition term89 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y2))) (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
