Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm737741_term_abbrevs.
Require Import thm737642_spec.
Require Import thm737645_spec.
Require Import thm737646_spec.
Lemma lem737723 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem737646 n) (@lem737645 n)). Qed.
Lemma lem737724 : term2 = term3.
Proof. exact (@lem737723 term4). Qed.
Lemma lem737726 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem737646 n) (@lem737645 n)). Qed.
Lemma lem737727 : term5 = term6.
Proof. exact (@lem737726 (BIT1 0)). Qed.
Lemma lem737729 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem737646 n) (@lem737645 n)). Qed.
Lemma lem737730 : term7 = term8.
Proof. exact (@lem737729 0). Qed.
Lemma lem737732 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem737642)). Qed.
Lemma lem737733 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem737734 : term8 = term9.
Proof. exact (MK_COMB (@lem737733) (@lem737732)). Qed.
Lemma lem737735 : term7 = term9.
Proof. exact (TRANS (@lem737730) (@lem737734)). Qed.
Lemma lem737736 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem737737 : term6 = term10.
Proof. exact (MK_COMB (@lem737736) (@lem737735)). Qed.
Lemma lem737738 : term5 = term10.
Proof. exact (TRANS (@lem737727) (@lem737737)). Qed.
Lemma lem737739 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem737740 : term3 = term11.
Proof. exact (MK_COMB (@lem737739) (@lem737738)). Qed.
Lemma lem737741 : term2 = term11.
Proof. exact (TRANS (@lem737724) (@lem737740)). Qed.
