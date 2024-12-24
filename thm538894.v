Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538894_term_abbrevs.
Require Import thm538851_spec.
Lemma lem538893 : term0.
Proof. exact (proj1 (@lem538851)). Qed.
Lemma lem538894 (n : nat) : term1 n.
Proof. exact (@lem538893 n). Qed.
