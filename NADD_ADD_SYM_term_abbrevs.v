Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_add y0 y1) = (mk_nadd (fun y2 : nat => Nat.add (dest_nadd y0 y2) (dest_nadd y1 y2)))) x0.
Definition term14 (x0 : nadd) (x1 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))) (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))).
Definition term11 (x0 : nadd) (x1 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x1 y0) (dest_nadd x0 y0))) (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))).
Definition term16 := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_add y0 y1) (nadd_add y1 y0).
Definition term12 (x0 : nadd) (x1 : nadd) (x2 : nat) := Nat.add (dest_nadd x0 x2) (dest_nadd x1 x2).
Definition term8 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_add x0 x1).
Definition term7 (x0 : nadd) (x1 : nadd) := mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0)).
Definition term15 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_add x0 y0) (nadd_add y0 x0).
Definition term6 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_add x0 y0) = (mk_nadd (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1)))) x1.
Definition term0 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term10 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_add x1 x0) (nadd_add x0 x1).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term5 (x0 : nadd) := forall y0 : nadd, (nadd_add x0 y0) = (mk_nadd (fun y1 : nat => Nat.add (dest_nadd x0 y1) (dest_nadd y0 y1))).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term13 (x0 : nadd) (x1 : nadd) := fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0).
Definition term9 (x0 : nadd) (x1 : nadd) := nadd_eq (mk_nadd (fun y0 : nat => Nat.add (dest_nadd x0 y0) (dest_nadd x1 y0))).
