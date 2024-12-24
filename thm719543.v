Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm719543_term_abbrevs.
Require Import thm719450_spec.
Require Import thm719453_spec.
Require Import thm719454_spec.
Lemma lem719531 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem719454 n) (@lem719453 n)). Qed.
Lemma lem719532 : term2 = term3.
Proof. exact (@lem719531 (BIT1 0)). Qed.
Lemma lem719534 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem719454 n) (@lem719453 n)). Qed.
Lemma lem719535 : term4 = term5.
Proof. exact (@lem719534 0). Qed.
Lemma lem719537 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem719450)). Qed.
Lemma lem719538 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem719539 : term5 = term6.
Proof. exact (MK_COMB (@lem719538) (@lem719537)). Qed.
Lemma lem719540 : term4 = term6.
Proof. exact (TRANS (@lem719535) (@lem719539)). Qed.
Lemma lem719541 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem719542 : term3 = term7.
Proof. exact (MK_COMB (@lem719541) (@lem719540)). Qed.
Lemma lem719543 : term2 = term7.
Proof. exact (TRANS (@lem719532) (@lem719542)). Qed.
