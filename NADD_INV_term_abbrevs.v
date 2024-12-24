Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 := @eq (nat -> nat) (fun y0 : nat => NUMERAL 0).
Definition term48 := forall y0 : nadd, (dest_nadd (nadd_inv y0)) = (@COND (nat -> nat) (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (fun y1 : nat => NUMERAL 0) (nadd_rinv y0)).
Definition term43 (x0 : nadd) := dest_nadd (mk_nadd (nadd_rinv x0)).
Definition term18 (x0 : nadd) := @eq (nat -> nat) (dest_nadd (@COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)))).
Definition term9 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term4 (x0 : nadd) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term20 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term40 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> (nadd_eq x0 (nadd_of_num (NUMERAL 0))) = False.
Definition term30 (x0 : nadd) := mk_nadd (nadd_rinv x0).
Definition term46 (x0 : nadd) := @COND (nat -> nat) False (fun y0 : nat => NUMERAL 0) (nadd_rinv x0).
Definition term21 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term39 (x0 : nadd) := @COND (nat -> nat) True (fun y0 : nat => NUMERAL 0) (nadd_rinv x0).
Definition term19 (x0 : nadd) := @COND (nat -> nat) (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (fun y0 : nat => NUMERAL 0) (nadd_rinv x0).
Definition term6 := (forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv y0 y3)) (Nat.mul y3 (nadd_rinv y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) -> forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv y0 y3)) (Nat.mul y3 (nadd_rinv y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term47 (x0 : nadd) := is_nadd (nadd_rinv x0).
Definition term41 := @COND nadd False (nadd_of_num (NUMERAL 0)).
Definition term45 := @COND (nat -> nat) False (fun y0 : nat => NUMERAL 0).
Definition term32 := dest_nadd (nadd_of_num (NUMERAL 0)).
Definition term7 (x0 : nat -> nat) := dest_nadd (mk_nadd x0).
Definition term44 (x0 : nadd) := @eq (nat -> nat) (dest_nadd (mk_nadd (nadd_rinv x0))).
Definition term5 (x0 : nadd) := (forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv y0 y3)) (Nat.mul y3 (nadd_rinv y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) -> exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term17 (x0 : nadd) := @eq (nat -> nat) (dest_nadd (nadd_inv x0)).
Definition term14 (x0 : nadd) := @COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)).
Definition term24 (x0 : nat) := dest_nadd (nadd_of_num x0).
Definition term34 := fun y0 : nat => NUMERAL 0.
Definition term27 := nadd_of_num (NUMERAL 0).
Definition term37 (x0 : nadd) := @COND (nat -> nat) (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (fun y0 : nat => NUMERAL 0).
Definition term8 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term1 (x0 : nadd) := (fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv y0 y3)) (Nat.mul y3 (nadd_rinv y0 y2)))) (Nat.mul y1 (Nat.add y2 y3))) x0.
Definition term10 (x0 : nadd) := (fun y0 : Prop => y0 \/ (~ y0)) (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term29 := @COND nadd True (nadd_of_num (NUMERAL 0)).
Definition term11 (x0 : nadd) := nadd_eq x0 (nadd_of_num (NUMERAL 0)).
Definition term13 (x0 : nadd) := (fun y0 : nadd => (nadd_inv y0) = (@COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0)))) x0.
Definition term38 := @COND (nat -> nat) True (fun y0 : nat => NUMERAL 0).
Definition term25 (x0 : nat) := fun y0 : nat => Nat.mul x0 y0.
Definition term23 (x0 : nat) := (fun y0 : nat => (dest_nadd (nadd_of_num y0)) = (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term33 := fun y0 : nat => Nat.mul (NUMERAL 0) y0.
Definition term0 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (nadd_rinv y0 y3)) (Nat.mul y3 (nadd_rinv y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)).
Definition term2 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (nadd_rinv x0 y2)) (Nat.mul y2 (nadd_rinv x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term16 (x0 : nadd) := dest_nadd (@COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0))).
Definition term28 (x0 : nadd) := @COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)).
Definition term12 (x0 : nadd) := (nadd_eq x0 (nadd_of_num (NUMERAL 0))) \/ (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))).
Definition term15 (x0 : nadd) := dest_nadd (nadd_inv x0).
Definition term42 (x0 : nadd) := @COND nadd False (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)).
Definition term3 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term22 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term31 (x0 : nadd) := @COND nadd True (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)).
Definition term36 (x0 : nadd) := @COND (nat -> nat) (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term26 (x0 : nadd) := @COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
