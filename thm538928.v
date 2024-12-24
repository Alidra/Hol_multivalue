Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538928_term_abbrevs.
Require Import thm538868_spec.
Require Import thm538869_spec.
Require Import thm538882_spec.
Require Import thm538883_spec.
Require Import thm538894_spec.
Require Import thm538895_spec.
Lemma lem538913 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem538883 m n) (@lem538882 m n)). Qed.
Lemma lem538914 : term2 = term3.
Proof. exact (@lem538913 (BIT1 0) term4). Qed.
Lemma lem538916 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem538869 m n) (@lem538868 m n)). Qed.
Lemma lem538917 : term7 = term8.
Proof. exact (@lem538916 0 (BIT1 0)). Qed.
Lemma lem538919 (n : nat) : (term9 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem538895 n) (@lem538894 n)). Qed.
Lemma lem538920 : term10 = (BIT1 0).
Proof. exact (@lem538919 0). Qed.
Lemma lem538921 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem538922 : term8 = term11.
Proof. exact (MK_COMB (@lem538921) (@lem538920)). Qed.
Lemma lem538923 : term7 = term11.
Proof. exact (TRANS (@lem538917) (@lem538922)). Qed.
Lemma lem538924 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem538925 : term3 = term12.
Proof. exact (MK_COMB (@lem538924) (@lem538923)). Qed.
Lemma lem538926 : term2 = term12.
Proof. exact (TRANS (@lem538914) (@lem538925)). Qed.
Lemma lem538927 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem538928 : term13 = term14.
Proof. exact (MK_COMB (@lem538927) (@lem538926)). Qed.
