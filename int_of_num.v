Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_of_num_term_abbrevs.
Lemma lem2271781 : int_of_num = term0.
Proof. exact (@int_of_num_def). Qed.
Lemma lem2271782 (_28662 : nat) : _28662 = _28662.
Proof. exact (eq_refl _28662). Qed.
Lemma lem2271783 (_28662 : nat) : (int_of_num _28662) = (term1 _28662).
Proof. exact (MK_COMB (@lem2271781) (@lem2271782 _28662)). Qed.
Lemma lem2271784 (_28662 : nat) : (term1 _28662) = (term2 _28662).
Proof. exact (eq_refl (term1 _28662)). Qed.
Lemma lem2271785 (_28662 : nat) : (int_of_num _28662) = (term2 _28662).
Proof. exact (TRANS (@lem2271783 _28662) (@lem2271784 _28662)). Qed.
Lemma lem2271786 : term3.
Proof. exact (fun _28662 : nat => @lem2271785 _28662). Qed.
Lemma lem2271787 (_28662 : nat) : term4 _28662.
Proof. exact (@lem2271786 _28662). Qed.
Lemma lem2271788 (_28662 : nat) : (term4 _28662) = ((int_of_num _28662) = (term2 _28662)).
Proof. exact (eq_refl (term4 _28662)). Qed.
Lemma lem2271789 (_28662 : nat) : (int_of_num _28662) = (term2 _28662).
Proof. exact (EQ_MP (@lem2271788 _28662) (@lem2271787 _28662)). Qed.
Lemma lem2271819 (n : nat) : (int_of_num n) = (term2 n).
Proof. exact (@lem2271789 n). Qed.
Lemma lem2271820 : term3.
Proof. exact (fun n : nat => @lem2271819 n). Qed.
