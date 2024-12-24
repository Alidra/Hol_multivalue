Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm521107_term_abbrevs.
Require Import LE_0_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem521095 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem521096 : (NUMERAL 0) = 0.
Proof. exact (@lem521095 0). Qed.
Lemma lem521097 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem521098 : term0 = (Peano.le 0).
Proof. exact (MK_COMB (@lem521097) (@lem521096)). Qed.
Lemma lem521099 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem521100 (n : nat) : (term1 n) = (Peano.le 0 n).
Proof. exact (MK_COMB (@lem521098) (@lem521099 n)). Qed.
Lemma lem521101 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem521100 n)). Qed.
Lemma lem521102 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521103 : term4 = term5.
Proof. exact (MK_COMB (@lem521102) (@lem521101)). Qed.
Lemma lem521104 : term5.
Proof. exact (EQ_MP (@lem521103) (@lem91499)). Qed.
Lemma lem521105 (n : nat) : term6 n.
Proof. exact (@lem521104 n). Qed.
Lemma lem521106 (n : nat) : (term6 n) = (Peano.le 0 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem521107 (n : nat) : Peano.le 0 n.
Proof. exact (EQ_MP (@lem521106 n) (@lem521105 n)). Qed.
