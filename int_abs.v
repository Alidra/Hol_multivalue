Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_abs_term_abbrevs.
Lemma lem2288087 : int_abs = term0.
Proof. exact (@int_abs_def). Qed.
Lemma lem2288088 (_28740 : int) : _28740 = _28740.
Proof. exact (eq_refl _28740). Qed.
Lemma lem2288089 (_28740 : int) : (int_abs _28740) = (term1 _28740).
Proof. exact (MK_COMB (@lem2288087) (@lem2288088 _28740)). Qed.
Lemma lem2288090 (_28740 : int) : (term1 _28740) = (term2 _28740).
Proof. exact (eq_refl (term1 _28740)). Qed.
Lemma lem2288091 (_28740 : int) : (int_abs _28740) = (term2 _28740).
Proof. exact (TRANS (@lem2288089 _28740) (@lem2288090 _28740)). Qed.
Lemma lem2288092 : term3.
Proof. exact (fun _28740 : int => @lem2288091 _28740). Qed.
Lemma lem2288093 (_28740 : int) : term4 _28740.
Proof. exact (@lem2288092 _28740). Qed.
Lemma lem2288094 (_28740 : int) : (term4 _28740) = ((int_abs _28740) = (term2 _28740)).
Proof. exact (eq_refl (term4 _28740)). Qed.
Lemma lem2288095 (_28740 : int) : (int_abs _28740) = (term2 _28740).
Proof. exact (EQ_MP (@lem2288094 _28740) (@lem2288093 _28740)). Qed.
Lemma lem2288125 (x : int) : (int_abs x) = (term2 x).
Proof. exact (@lem2288095 x). Qed.
Lemma lem2288126 : term3.
Proof. exact (fun x : int => @lem2288125 x). Qed.
