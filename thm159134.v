Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm159134_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Lemma lem159132 (n : nat) : term0 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem159133 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem159134 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem159133 n) (@lem159132 n)). Qed.
