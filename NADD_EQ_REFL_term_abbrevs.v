Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (dest_nadd y0 y3) (dest_nadd y1 y3))) y2)) x0.
Definition term8 (x0 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y1))) y0.
Definition term7 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x1 y1))) y0.
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (x0 : nadd) (x1 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 y0))) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term20 := exists y0 : nat, True.
Definition term6 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1)) x1.
Definition term22 (x0 : Prop) := exists y0 : nat, x0.
Definition term3 (x0 : nat) := dist (@pair nat nat x0 x0).
Definition term16 := forall y0 : nat, True.
Definition term23 := forall y0 : nadd, nadd_eq y0 y0.
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term14 := fun y0 : nat => True.
Definition term21 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term10 (x0 : nadd) (x1 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 x1))).
Definition term19 (x0 : nadd) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y1) (dest_nadd x0 y1))) y0.
Definition term15 (x0 : nadd) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y0) (dest_nadd x0 y0))) x1.
Definition term12 (x0 : nadd) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 x1))) x2.
Definition term18 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (dest_nadd x0 y2) (dest_nadd y0 y2))) y1).
Definition term11 := Peano.le (NUMERAL 0).
Definition term2 (x0 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 y0)) = (NUMERAL 0)) x0.
Definition term9 (x0 : nadd) (x1 : nat) := dist (@pair nat nat (dest_nadd x0 x1) (dest_nadd x0 x1)).
