Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term7 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term1 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0)).
Definition term16 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (nadd_eq y0 x0).
Definition term17 := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0).
Definition term9 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0).
Definition term3 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term13 (x0 : nadd) (x1 : nadd) (x2 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term11 (x0 : nadd) (x1 : nadd) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))).
Definition term6 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term10 (x0 : nadd) (x1 : nadd) (x2 : nat) := dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2)).
Definition term14 (x0 : nadd) (x1 : nadd) (x2 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x1 y0))) x2.
Definition term15 (x0 : nadd) (x1 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y0 y1)) = (dist (@pair nat nat y1 y0))) x0.
Definition term12 (x0 : nadd) (x1 : nadd) (x2 : nat) (x3 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x2) (dest_nadd x1 x2))) x3.
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat x0 y0)) = (dist (@pair nat nat y0 x0))) x1.
Definition term8 (x0 : nadd) (x1 : nadd) := @eq Prop (nadd_eq x0 x1).
