Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032095_spec.
Lemma lem1032098 (c : nat) (a : nat) : (Nat.add a c) = (Nat.add c a).
Proof. exact (proj1 (@lem1032095 a c (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
