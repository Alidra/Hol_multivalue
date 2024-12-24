Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538330_term_abbrevs.
Require Import thm538283_spec.
Require Import thm538284_spec.
Require Import thm538294_spec.
Require Import thm538295_spec.
Lemma lem538321 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem538284 m n) (@lem538283 m n)). Qed.
Lemma lem538322 : term2 = term3.
Proof. exact (@lem538321 (BIT1 0) 0). Qed.
Lemma lem538324 (n : nat) : (term4 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem538295 n) (@lem538294 n)). Qed.
Lemma lem538325 : term5 = (BIT1 0).
Proof. exact (@lem538324 0). Qed.
Lemma lem538326 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem538327 : term3 = term6.
Proof. exact (MK_COMB (@lem538326) (@lem538325)). Qed.
Lemma lem538328 : term2 = term6.
Proof. exact (TRANS (@lem538322) (@lem538327)). Qed.
Lemma lem538329 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem538330 : term7 = term8.
Proof. exact (MK_COMB (@lem538329) (@lem538328)). Qed.
