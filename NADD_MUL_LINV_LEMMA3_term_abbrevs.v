Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term65 (x0 : nadd) := (exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1)) -> exists y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul (dest_nadd x0 y2) (nadd_rinv x0 y2)))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul y2 y2))))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2))).
Definition term50 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x0 (Nat.mul (dest_nadd x1 x0) (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)))) (Nat.mul x0 (Nat.mul (dest_nadd x1 x0) (Nat.mul x2 x2))))) (Nat.mul x0 (Nat.mul (dest_nadd x1 x0) (dest_nadd x1 x2))).
Definition term46 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x1 (Nat.mul (dest_nadd x0 x1) (Nat.mul (dest_nadd x0 x2) (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.mul (dest_nadd x0 x1) (Nat.mul x2 x2))))).
Definition term62 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul (dest_nadd x0 y2) (nadd_rinv x0 y2)))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul y2 y2))))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2))).
Definition term34 (x0 : nadd) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (Nat.mul (dest_nadd x2 y0) (nadd_rinv x2 y0)))) (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (Nat.mul y0 y0))))) (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (dest_nadd x2 y0))).
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2)))) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.mul y1 y2)) = (Nat.mul (Nat.mul y0 y1) y2)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 x2)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0)) x2.
Definition term38 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (dest_nadd x1 x0) (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)).
Definition term40 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.mul (dest_nadd x0 x2) (nadd_rinv x0 x2))) (Nat.mul (dest_nadd x0 x1) (Nat.mul x2 x2))).
Definition term45 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (dist (@pair nat nat x1 x2)).
Definition term24 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x0 (Nat.mul x1 y0)) = (Nat.mul (Nat.mul x0 x1) y0).
Definition term56 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1)) (Nat.mul x1 x1))) (dest_nadd x0 x1).
Definition term39 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.mul (dest_nadd x0 x1) (Nat.mul x2 x2).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1)))) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term47 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x0 (dest_nadd x1 x0)) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2)))).
Definition term43 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (Nat.mul (dest_nadd x1 x0) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2)))).
Definition term51 (x0 : nat) (x1 : nadd) (x2 : nat) := Peano.le (Nat.mul (Nat.mul x0 (dest_nadd x1 x0)) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2)))) (Nat.mul (Nat.mul x0 (dest_nadd x1 x0)) (dest_nadd x1 x2)).
Definition term36 (x0 : nadd) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x1 (Nat.mul (dest_nadd x0 x1) (Nat.mul (dest_nadd x0 x2) (nadd_rinv x0 x2)))) (Nat.mul x1 (Nat.mul (dest_nadd x0 x1) (Nat.mul x2 x2)))).
Definition term52 (x0 : nat) (x1 : nadd) (x2 : nat) := ((Nat.mul x0 (dest_nadd x1 x0)) = (NUMERAL 0)) \/ (Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))) (dest_nadd x1 x2)).
Definition term54 (x0 : nat) (x1 : nadd) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0)) x2.
Definition term35 (x0 : nat) (x1 : nadd) := forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0).
Definition term57 (x0 : nat) (x1 : nadd) (x2 : nat) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0)) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))) (dest_nadd x1 x2).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term61 (x0 : nat) (x1 : nadd) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul y0 (Nat.mul (dest_nadd x1 y0) (Nat.mul (dest_nadd x1 y1) (nadd_rinv x1 y1)))) (Nat.mul y0 (Nat.mul (dest_nadd x1 y0) (Nat.mul y1 y1))))) (Nat.mul y0 (Nat.mul (dest_nadd x1 y0) (dest_nadd x1 y1))).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.mul y0 y1)) = (Nat.mul (Nat.mul x0 y0) y1).
Definition term20 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term19 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))).
Definition term16 (x0 : nat) := forall y0 : nat, forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1))).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term42 (x0 : nadd) (x1 : nat) := Nat.mul (dest_nadd x0 x1) (nadd_rinv x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0))).
Definition term31 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd y0 y2) (nadd_rinv y0 y2)) (Nat.mul y2 y2))) (dest_nadd y0 y2)) x0.
Definition term48 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul x0 (Nat.mul (dest_nadd x1 x0) (dest_nadd x1 x2)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term67 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le y1 y3) -> Peano.le (dist (@pair nat nat (Nat.mul y2 (Nat.mul (dest_nadd y0 y2) (Nat.mul (dest_nadd y0 y3) (nadd_rinv y0 y3)))) (Nat.mul y2 (Nat.mul (dest_nadd y0 y2) (Nat.mul y3 y3))))) (Nat.mul y2 (Nat.mul (dest_nadd y0 y2) (dest_nadd y0 y3))).
Definition term49 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x0 (dest_nadd x1 x0)) (dest_nadd x1 x2).
Definition term66 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul (dest_nadd x0 y2) (nadd_rinv x0 y2)))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul y2 y2))))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2))).
Definition term32 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term55 (x0 : nat) (x1 : nadd) (x2 : nat) := (Peano.le x0 x2) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))) (dest_nadd x1 x2).
Definition term13 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul x0 (dist (@pair nat nat y0 y1))) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))).
Definition term33 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term37 (x0 : nadd) (x1 : nat) (x2 : nat) := Nat.mul x1 (dist (@pair nat nat (Nat.mul (dest_nadd x0 x1) (Nat.mul (dest_nadd x0 x2) (nadd_rinv x0 x2))) (Nat.mul (dest_nadd x0 x1) (Nat.mul x2 x2)))).
Definition term44 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (Nat.mul x0 (dest_nadd x1 x0)) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nadd) (x3 : nat) := (Peano.le x0 x3) -> Peano.le (dist (@pair nat nat (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (Nat.mul (dest_nadd x2 x3) (nadd_rinv x2 x3)))) (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (Nat.mul x3 x3))))) (Nat.mul x1 (Nat.mul (dest_nadd x2 x1) (dest_nadd x2 x3))).
Definition term9 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul x1 (dist (@pair nat nat x0 y0))) = (dist (@pair nat nat (Nat.mul x1 x0) (Nat.mul x1 y0))).
Definition term53 (x0 : nadd) (x1 : nat) := Nat.mul x1 (dest_nadd x0 x1).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (dist (@pair nat nat (Nat.mul x0 x1) (Nat.mul x0 y0))) = (Nat.mul x0 (dist (@pair nat nat x1 y0)))) x2.
Definition term41 (x0 : nat) (x1 : nadd) (x2 : nat) := Nat.mul (dest_nadd x1 x0) (dist (@pair nat nat (Nat.mul (dest_nadd x1 x2) (nadd_rinv x1 x2)) (Nat.mul x2 x2))).
Definition term64 (x0 : nadd) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x0 y1) (nadd_rinv x0 y1)) (Nat.mul y1 y1))) (dest_nadd x0 y1).
Definition term14 (x0 : nat) := fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x0 y1))) = (Nat.mul x0 (dist (@pair nat nat y0 y1))).
Definition term63 (x0 : nadd) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y2) -> Peano.le (dist (@pair nat nat (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul (dest_nadd x0 y2) (nadd_rinv x0 y2)))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (Nat.mul y2 y2))))) (Nat.mul y1 (Nat.mul (dest_nadd x0 y1) (dest_nadd x0 y2))).
Definition term18 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))) = (Nat.mul y0 (dist (@pair nat nat y1 y2))).
Definition term17 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (dist (@pair nat nat y1 y2))) = (dist (@pair nat nat (Nat.mul y0 y1) (Nat.mul y0 y2))).
Definition term58 (x0 : nat) (x1 : nadd) := (forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0)) -> forall y0 : nat, (Peano.le x0 y0) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x1 y0) (nadd_rinv x1 y0)) (Nat.mul y0 y0))) (dest_nadd x1 y0).
