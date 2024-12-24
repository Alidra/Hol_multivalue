Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365988_term_abbrevs.
Require Import thm1365987_spec.
Lemma lem1365988 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem1365987 m n)). Qed.
