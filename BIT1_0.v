Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT1_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem512848 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem512849 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem512854 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512849 n) (@lem512848 n)). Qed.
Lemma lem512855 : (NUMERAL 0) = 0.
Proof. exact (@lem512854 0). Qed.
Lemma lem512856 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem512857 : term1 = (BIT1 0).
Proof. exact (MK_COMB (@lem512856) (@lem512855)). Qed.
Lemma lem512858 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem512859 : term2 = term3.
Proof. exact (MK_COMB (@lem512858) (@lem512857)). Qed.
Lemma lem512861 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512849 n) (@lem512848 n)). Qed.
Lemma lem512862 : term4 = (BIT1 0).
Proof. exact (@lem512861 (BIT1 0)). Qed.
Lemma lem512863 : (term1 = term4) = ((BIT1 0) = (BIT1 0)).
Proof. exact (MK_COMB (@lem512859) (@lem512862)). Qed.
Lemma lem512865 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem512866 (x : nat) : (x = x) = True.
Proof. exact (@lem512865 nat x). Qed.
Lemma lem512867 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (@lem512866 (BIT1 0)). Qed.
Lemma lem512868 : (term1 = term4) = True.
Proof. exact (TRANS (@lem512863) (@lem512867)). Qed.
Lemma lem512869 : True = (term1 = term4).
Proof. exact (SYM (@lem512868)). Qed.
Lemma lem512870 : term1 = term4.
Proof. exact (EQ_MP (@lem512869) (@lem0)). Qed.
