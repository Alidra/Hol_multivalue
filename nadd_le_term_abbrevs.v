Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2))) x0.
Definition term4 (x0 : nadd) (x1 : nadd) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (dest_nadd x1 y1) y0).
Definition term6 := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) = (exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2)).
Definition term0 := fun y0 : nadd => fun y1 : nadd => exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2).
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)) x1.
Definition term2 (x0 : nadd) := fun y0 : nadd => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1).
Definition term8 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1))) x1.
Definition term1 (x0 : nadd) := (fun y0 : nadd => fun y1 : nadd => exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (dest_nadd y1 y3) y2)) x0.
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) = (exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (dest_nadd y0 y2) y1)).
