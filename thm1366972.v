Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1366972_term_abbrevs.
Require Import thm1366971_spec.
Lemma lem1366972 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem1366971 m n)). Qed.
