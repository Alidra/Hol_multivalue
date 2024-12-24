Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term9 := forall y0 : nat, real_le (real_of_num (NUMERAL 0)) (real_of_num y0).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term6 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term10 := forall y0 : nat, True.
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term8 := fun y0 : nat => True.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term12 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term7 := fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0).
