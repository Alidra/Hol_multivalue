Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528273_term_abbrevs.
Require Import thm528180_spec.
Require Import thm528183_spec.
Require Import thm528184_spec.
Require Import thm528240_spec.
Require Import thm528241_spec.
Lemma lem528259 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem528241 n) (@lem528240 n)). Qed.
Lemma lem528260 : term1 = (BIT1 0).
Proof. exact (@lem528259 0). Qed.
Lemma lem528261 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem528262 : term2 = term3.
Proof. exact (MK_COMB (@lem528261) (@lem528260)). Qed.
Lemma lem528264 (n : nat) : (term4 n) = (term5 n).
Proof. exact (EQ_MP (@lem528184 n) (@lem528183 n)). Qed.
Lemma lem528265 : term3 = term6.
Proof. exact (@lem528264 0). Qed.
Lemma lem528267 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem528180)). Qed.
Lemma lem528268 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem528269 : term6 = term7.
Proof. exact (MK_COMB (@lem528268) (@lem528267)). Qed.
Lemma lem528270 : term3 = term7.
Proof. exact (TRANS (@lem528265) (@lem528269)). Qed.
Lemma lem528271 : term2 = term7.
Proof. exact (TRANS (@lem528262) (@lem528270)). Qed.
Lemma lem528272 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem528273 : term8 = term9.
Proof. exact (MK_COMB (@lem528272) (@lem528271)). Qed.
