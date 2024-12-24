Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => (@list_of_seq a0 y0 (NUMERAL 0)) = (@nil a0)) x0.
Definition term0 (a0 : Type') := forall y0 : nat -> a0, (@list_of_seq a0 y0 (NUMERAL 0)) = (@nil a0).
