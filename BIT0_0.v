Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT0_0_term_abbrevs.
Require Import ARITH_ZERO_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem512822 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem512823 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem512828 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512823 n) (@lem512822 n)). Qed.
Lemma lem512829 : (NUMERAL 0) = 0.
Proof. exact (@lem512828 0). Qed.
Lemma lem512830 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem512831 : term1 = (BIT0 0).
Proof. exact (MK_COMB (@lem512830) (@lem512829)). Qed.
Lemma lem512833 : (BIT0 0) = 0.
Proof. exact (proj2 (@lem512819)). Qed.
Lemma lem512834 : term1 = 0.
Proof. exact (TRANS (@lem512831) (@lem512833)). Qed.
Lemma lem512835 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512836 : term2 = (@eq nat 0).
Proof. exact (MK_COMB (@lem512835) (@lem512834)). Qed.
Lemma lem512838 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512823 n) (@lem512822 n)). Qed.
Lemma lem512839 : (NUMERAL 0) = 0.
Proof. exact (@lem512838 0). Qed.
Lemma lem512840 : (term1 = (NUMERAL 0)) = (0 = 0).
Proof. exact (MK_COMB (@lem512836) (@lem512839)). Qed.
Lemma lem512842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512843 (x : nat) : (x = x) = True.
Proof. exact (@lem512842 nat x). Qed.
Lemma lem512844 : (0 = 0) = True.
Proof. exact (@lem512843 0). Qed.
Lemma lem512845 : (term1 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem512840) (@lem512844)). Qed.
Lemma lem512846 : True = (term1 = (NUMERAL 0)).
Proof. exact (SYM (@lem512845)). Qed.
Lemma lem512847 : term1 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem512846) (@lem0)). Qed.
