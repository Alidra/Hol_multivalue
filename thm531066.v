Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531066_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem531005 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem531006 : term1.
Proof. exact (proj2 (@lem531005)). Qed.
Lemma lem531007 : term2.
Proof. exact (proj2 (@lem531006)). Qed.
Lemma lem531008 : term3.
Proof. exact (proj2 (@lem531007)). Qed.
Lemma lem531045 : term4.
Proof. exact (proj1 (@lem531008)). Qed.
Lemma lem531046 (n : nat) : term5 n.
Proof. exact (@lem531045 n). Qed.
Lemma lem531047 (n : nat) : (term5 n) = ((term6 n) = (BIT0 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem531066 (n : nat) : (term6 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem531047 n) (@lem531046 n)). Qed.
