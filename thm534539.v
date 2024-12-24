Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm534539_term_abbrevs.
Require Import thm534446_spec.
Require Import thm534449_spec.
Require Import thm534450_spec.
Require Import thm534498_spec.
Require Import thm534499_spec.
Lemma lem534525 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem534499 n) (@lem534498 n)). Qed.
Lemma lem534526 : term1 = (BIT1 0).
Proof. exact (@lem534525 0). Qed.
Lemma lem534527 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem534528 : term2 = term3.
Proof. exact (MK_COMB (@lem534527) (@lem534526)). Qed.
Lemma lem534530 (n : nat) : (term4 n) = (term5 n).
Proof. exact (EQ_MP (@lem534450 n) (@lem534449 n)). Qed.
Lemma lem534531 : term3 = term6.
Proof. exact (@lem534530 0). Qed.
Lemma lem534533 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem534446)). Qed.
Lemma lem534534 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem534535 : term6 = term7.
Proof. exact (MK_COMB (@lem534534) (@lem534533)). Qed.
Lemma lem534536 : term3 = term7.
Proof. exact (TRANS (@lem534531) (@lem534535)). Qed.
Lemma lem534537 : term2 = term7.
Proof. exact (TRANS (@lem534528) (@lem534536)). Qed.
Lemma lem534538 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem534539 : term8 = term9.
Proof. exact (MK_COMB (@lem534538) (@lem534537)). Qed.
