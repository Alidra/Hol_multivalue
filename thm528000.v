Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528000_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem527939 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem527940 : term1.
Proof. exact (proj2 (@lem527939)). Qed.
Lemma lem527941 : term2.
Proof. exact (proj2 (@lem527940)). Qed.
Lemma lem527942 : term3.
Proof. exact (proj2 (@lem527941)). Qed.
Lemma lem527943 : term4.
Proof. exact (proj2 (@lem527942)). Qed.
Lemma lem527975 : term5.
Proof. exact (proj1 (@lem527943)). Qed.
Lemma lem527976 (n : nat) : term6 n.
Proof. exact (@lem527975 n). Qed.
Lemma lem527977 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem528000 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem527977 n) (@lem527976 n)). Qed.
