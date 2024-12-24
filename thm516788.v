Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516788_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516779 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516780 : (NUMERAL 0) = 0.
Proof. exact (@lem516779 0). Qed.
Lemma lem516781 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516782 (n : nat) : ((S n) = (NUMERAL 0)) = ((S n) = 0).
Proof. exact (MK_COMB (@lem516781 n) (@lem516780)). Qed.
Lemma lem516783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516784 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem516783) (@lem516782 n)). Qed.
Lemma lem516785 : term3 = term4.
Proof. exact (fun_ext (fun n : nat => @lem516784 n)). Qed.
Lemma lem516786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516787 : term5 = term6.
Proof. exact (MK_COMB (@lem516786) (@lem516785)). Qed.
Lemma lem516788 : term6.
Proof. exact (EQ_MP (@lem516787) (@lem75570)). Qed.
