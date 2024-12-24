Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nadd) := fun y0 : nat => Nat.div (Nat.mul y0 y0) (dest_nadd x0 y0).
Definition term3 := forall y0 : nadd, (nadd_rinv y0) = (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1)).
Definition term1 (x0 : nadd) := (fun y0 : nadd => fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1)) x0.
Definition term4 (x0 : nadd) := (fun y0 : nadd => (nadd_rinv y0) = (fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1))) x0.
Definition term0 := fun y0 : nadd => fun y1 : nat => Nat.div (Nat.mul y1 y1) (dest_nadd y0 y1).
