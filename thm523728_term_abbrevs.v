Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
