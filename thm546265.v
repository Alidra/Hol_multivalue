Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546265_term_abbrevs.
Require Import thm546166_spec.
Require Import thm546169_spec.
Require Import thm546170_spec.
Require Import thm546193_spec.
Require Import thm546194_spec.
Require Import thm546218_spec.
Require Import thm546219_spec.
Lemma lem546245 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem546194 m n) (@lem546193 m n)). Qed.
Lemma lem546246 : term2 = term3.
Proof. exact (@lem546245 (BIT1 0) 0). Qed.
Lemma lem546248 (n : nat) : (term4 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem546219 n) (@lem546218 n)). Qed.
Lemma lem546249 : term5 = (BIT1 0).
Proof. exact (@lem546248 0). Qed.
Lemma lem546250 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem546251 : term6 = term7.
Proof. exact (MK_COMB (@lem546250) (@lem546249)). Qed.
Lemma lem546253 (n : nat) : (term8 n) = (term9 n).
Proof. exact (EQ_MP (@lem546170 n) (@lem546169 n)). Qed.
Lemma lem546254 : term7 = term10.
Proof. exact (@lem546253 0). Qed.
Lemma lem546256 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem546166)). Qed.
Lemma lem546257 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem546258 : term10 = term11.
Proof. exact (MK_COMB (@lem546257) (@lem546256)). Qed.
Lemma lem546259 : term7 = term11.
Proof. exact (TRANS (@lem546254) (@lem546258)). Qed.
Lemma lem546260 : term6 = term11.
Proof. exact (TRANS (@lem546251) (@lem546259)). Qed.
Lemma lem546261 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem546262 : term3 = term12.
Proof. exact (MK_COMB (@lem546261) (@lem546260)). Qed.
Lemma lem546263 : term2 = term12.
Proof. exact (TRANS (@lem546246) (@lem546262)). Qed.
Lemma lem546264 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem546265 : term13 = term14.
Proof. exact (MK_COMB (@lem546264) (@lem546263)). Qed.
