Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637143_term_abbrevs.
Require Import HAS_SIZE_NUMSEG_1_spec.
Lemma lem7637141 (n : nat) : term0 n.
Proof. exact (@lem5400760 n). Qed.
Lemma lem7637142 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7637143 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem7637142 n) (@lem7637141 n)). Qed.
