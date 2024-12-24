Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_pow_term_abbrevs.
Lemma lem2293995 : int_pow = term0.
Proof. exact (@int_pow_def). Qed.
Lemma lem2293996 (_28847 : int) : _28847 = _28847.
Proof. exact (eq_refl _28847). Qed.
Lemma lem2293997 (_28847 : int) : (int_pow _28847) = (term1 _28847).
Proof. exact (MK_COMB (@lem2293995) (@lem2293996 _28847)). Qed.
Lemma lem2293998 (_28847 : int) : (term1 _28847) = (term2 _28847).
Proof. exact (eq_refl (term1 _28847)). Qed.
Lemma lem2293999 (_28847 : int) : (int_pow _28847) = (term2 _28847).
Proof. exact (TRANS (@lem2293997 _28847) (@lem2293998 _28847)). Qed.
Lemma lem2294000 (_28848 : nat) : _28848 = _28848.
Proof. exact (eq_refl _28848). Qed.
Lemma lem2294001 (_28847 : int) (_28848 : nat) : (int_pow _28847 _28848) = (term3 _28847 _28848).
Proof. exact (MK_COMB (@lem2293999 _28847) (@lem2294000 _28848)). Qed.
Lemma lem2294002 (_28847 : int) (_28848 : nat) : (term3 _28847 _28848) = (term4 _28847 _28848).
Proof. exact (eq_refl (term3 _28847 _28848)). Qed.
Lemma lem2294003 (_28847 : int) (_28848 : nat) : (int_pow _28847 _28848) = (term4 _28847 _28848).
Proof. exact (TRANS (@lem2294001 _28847 _28848) (@lem2294002 _28847 _28848)). Qed.
Lemma lem2294004 (_28847 : int) : term5 _28847.
Proof. exact (fun _28848 : nat => @lem2294003 _28847 _28848). Qed.
Lemma lem2294005 : term6.
Proof. exact (fun _28847 : int => @lem2294004 _28847). Qed.
Lemma lem2294006 (_28847 : int) : term7 _28847.
Proof. exact (@lem2294005 _28847). Qed.
Lemma lem2294007 (_28847 : int) : (term7 _28847) = (term5 _28847).
Proof. exact (eq_refl (term7 _28847)). Qed.
Lemma lem2294008 (_28847 : int) : term5 _28847.
Proof. exact (EQ_MP (@lem2294007 _28847) (@lem2294006 _28847)). Qed.
Lemma lem2294009 (_28847 : int) (_28848 : nat) : term8 _28847 _28848.
Proof. exact (@lem2294008 _28847 _28848). Qed.
Lemma lem2294010 (_28847 : int) (_28848 : nat) : (term8 _28847 _28848) = ((int_pow _28847 _28848) = (term4 _28847 _28848)).
Proof. exact (eq_refl (term8 _28847 _28848)). Qed.
Lemma lem2294011 (_28847 : int) (_28848 : nat) : (int_pow _28847 _28848) = (term4 _28847 _28848).
Proof. exact (EQ_MP (@lem2294010 _28847 _28848) (@lem2294009 _28847 _28848)). Qed.
Lemma lem2294054 (x : int) (n : nat) : (int_pow x n) = (term4 x n).
Proof. exact (@lem2294011 x n). Qed.
Lemma lem2294055 (x : int) : term5 x.
Proof. exact (fun n : nat => @lem2294054 x n). Qed.
Lemma lem2294056 : term6.
Proof. exact (fun x : int => @lem2294055 x). Qed.
