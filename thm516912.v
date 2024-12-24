Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516912_term_abbrevs.
Require Import LE_0_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516900 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516901 : (NUMERAL 0) = 0.
Proof. exact (@lem516900 0). Qed.
Lemma lem516902 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem516903 : term0 = (Peano.le 0).
Proof. exact (MK_COMB (@lem516902) (@lem516901)). Qed.
Lemma lem516904 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem516905 (n : nat) : (term1 n) = (Peano.le 0 n).
Proof. exact (MK_COMB (@lem516903) (@lem516904 n)). Qed.
Lemma lem516906 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem516905 n)). Qed.
Lemma lem516907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516908 : term4 = term5.
Proof. exact (MK_COMB (@lem516907) (@lem516906)). Qed.
Lemma lem516909 : term5.
Proof. exact (EQ_MP (@lem516908) (@lem91499)). Qed.
Lemma lem516910 (n : nat) : term6 n.
Proof. exact (@lem516909 n). Qed.
Lemma lem516911 (n : nat) : (term6 n) = (Peano.le 0 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem516912 (n : nat) : Peano.le 0 n.
Proof. exact (EQ_MP (@lem516911 n) (@lem516910 n)). Qed.
