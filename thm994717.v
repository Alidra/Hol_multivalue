Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm994716_spec.
Lemma lem994717 (m : nat) : (Nat.mul m 0) = 0.
Proof. exact (proj2 (@lem994716 (@el nat) m)). Qed.
