Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7640394_spec.
Lemma lem7640396 {M N : Type'} : @FINITE (finite_sum M N) (@UNIV (finite_sum M N)).
Proof. exact (proj1 (@lem7640394 M N)). Qed.
