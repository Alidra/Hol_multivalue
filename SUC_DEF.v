Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUC_DEF_term_abbrevs.
Lemma lem71554 : S = term0.
Proof. exact (@SUC_def). Qed.
Lemma lem71555 (_2104 : nat) : _2104 = _2104.
Proof. exact (eq_refl _2104). Qed.
Lemma lem71556 (_2104 : nat) : (S _2104) = (term1 _2104).
Proof. exact (MK_COMB (@lem71554) (@lem71555 _2104)). Qed.
Lemma lem71557 (_2104 : nat) : (term1 _2104) = (term2 _2104).
Proof. exact (eq_refl (term1 _2104)). Qed.
Lemma lem71558 (_2104 : nat) : (S _2104) = (term2 _2104).
Proof. exact (TRANS (@lem71556 _2104) (@lem71557 _2104)). Qed.
Lemma lem71559 : term3.
Proof. exact (fun _2104 : nat => @lem71558 _2104). Qed.
Lemma lem71560 (_2104 : nat) : term4 _2104.
Proof. exact (@lem71559 _2104). Qed.
Lemma lem71561 (_2104 : nat) : (term4 _2104) = ((S _2104) = (term2 _2104)).
Proof. exact (eq_refl (term4 _2104)). Qed.
Lemma lem71562 (_2104 : nat) : (S _2104) = (term2 _2104).
Proof. exact (EQ_MP (@lem71561 _2104) (@lem71560 _2104)). Qed.
Lemma lem71592 (n : nat) : (S n) = (term2 n).
Proof. exact (@lem71562 n). Qed.
Lemma lem71593 : term3.
Proof. exact (fun n : nat => @lem71592 n). Qed.
