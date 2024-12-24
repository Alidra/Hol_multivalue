Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : nat => mk_nadd (fun y1 : nat => Nat.mul y0 y1).
Definition term1 (x0 : nat) := (fun y0 : nat => mk_nadd (fun y1 : nat => Nat.mul y0 y1)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => (nadd_of_num y0) = (mk_nadd (fun y1 : nat => Nat.mul y0 y1))) x0.
Definition term2 (x0 : nat) := mk_nadd (fun y0 : nat => Nat.mul x0 y0).
Definition term3 := forall y0 : nat, (nadd_of_num y0) = (mk_nadd (fun y1 : nat => Nat.mul y0 y1)).
