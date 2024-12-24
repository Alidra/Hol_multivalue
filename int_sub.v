Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_sub_term_abbrevs.
Lemma lem2285370 : int_sub = term0.
Proof. exact (@int_sub_def). Qed.
Lemma lem2285371 (_28708 : int) : _28708 = _28708.
Proof. exact (eq_refl _28708). Qed.
Lemma lem2285372 (_28708 : int) : (int_sub _28708) = (term1 _28708).
Proof. exact (MK_COMB (@lem2285370) (@lem2285371 _28708)). Qed.
Lemma lem2285373 (_28708 : int) : (term1 _28708) = (term2 _28708).
Proof. exact (eq_refl (term1 _28708)). Qed.
Lemma lem2285374 (_28708 : int) : (int_sub _28708) = (term2 _28708).
Proof. exact (TRANS (@lem2285372 _28708) (@lem2285373 _28708)). Qed.
Lemma lem2285375 (_28709 : int) : _28709 = _28709.
Proof. exact (eq_refl _28709). Qed.
Lemma lem2285376 (_28708 : int) (_28709 : int) : (int_sub _28708 _28709) = (term3 _28708 _28709).
Proof. exact (MK_COMB (@lem2285374 _28708) (@lem2285375 _28709)). Qed.
Lemma lem2285377 (_28708 : int) (_28709 : int) : (term3 _28708 _28709) = (term4 _28708 _28709).
Proof. exact (eq_refl (term3 _28708 _28709)). Qed.
Lemma lem2285378 (_28708 : int) (_28709 : int) : (int_sub _28708 _28709) = (term4 _28708 _28709).
Proof. exact (TRANS (@lem2285376 _28708 _28709) (@lem2285377 _28708 _28709)). Qed.
Lemma lem2285379 (_28708 : int) : term5 _28708.
Proof. exact (fun _28709 : int => @lem2285378 _28708 _28709). Qed.
Lemma lem2285380 : term6.
Proof. exact (fun _28708 : int => @lem2285379 _28708). Qed.
Lemma lem2285381 (_28708 : int) : term7 _28708.
Proof. exact (@lem2285380 _28708). Qed.
Lemma lem2285382 (_28708 : int) : (term7 _28708) = (term5 _28708).
Proof. exact (eq_refl (term7 _28708)). Qed.
Lemma lem2285383 (_28708 : int) : term5 _28708.
Proof. exact (EQ_MP (@lem2285382 _28708) (@lem2285381 _28708)). Qed.
Lemma lem2285384 (_28708 : int) (_28709 : int) : term8 _28708 _28709.
Proof. exact (@lem2285383 _28708 _28709). Qed.
Lemma lem2285385 (_28708 : int) (_28709 : int) : (term8 _28708 _28709) = ((int_sub _28708 _28709) = (term4 _28708 _28709)).
Proof. exact (eq_refl (term8 _28708 _28709)). Qed.
Lemma lem2285386 (_28708 : int) (_28709 : int) : (int_sub _28708 _28709) = (term4 _28708 _28709).
Proof. exact (EQ_MP (@lem2285385 _28708 _28709) (@lem2285384 _28708 _28709)). Qed.
Lemma lem2285429 (x : int) (y : int) : (int_sub x y) = (term4 x y).
Proof. exact (@lem2285386 x y). Qed.
Lemma lem2285430 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2285429 x y). Qed.
Lemma lem2285431 : term6.
Proof. exact (fun x : int => @lem2285430 x). Qed.
