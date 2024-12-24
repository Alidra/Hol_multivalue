Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm994716_spec.
Lemma lem994718 (n : nat) : (Nat.mul 0 n) = 0.
Proof. exact (proj1 (@lem994716 n (@el nat))). Qed.
