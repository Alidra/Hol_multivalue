Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_ge_term_abbrevs.
Lemma lem2270391 : int_ge = term0.
Proof. exact (@int_ge_def). Qed.
Lemma lem2270392 (_28638 : int) : _28638 = _28638.
Proof. exact (eq_refl _28638). Qed.
Lemma lem2270393 (_28638 : int) : (int_ge _28638) = (term1 _28638).
Proof. exact (MK_COMB (@lem2270391) (@lem2270392 _28638)). Qed.
Lemma lem2270394 (_28638 : int) : (term1 _28638) = (term2 _28638).
Proof. exact (eq_refl (term1 _28638)). Qed.
Lemma lem2270395 (_28638 : int) : (int_ge _28638) = (term2 _28638).
Proof. exact (TRANS (@lem2270393 _28638) (@lem2270394 _28638)). Qed.
Lemma lem2270396 (_28639 : int) : _28639 = _28639.
Proof. exact (eq_refl _28639). Qed.
Lemma lem2270397 (_28638 : int) (_28639 : int) : (int_ge _28638 _28639) = (term3 _28638 _28639).
Proof. exact (MK_COMB (@lem2270395 _28638) (@lem2270396 _28639)). Qed.
Lemma lem2270398 (_28638 : int) (_28639 : int) : (term3 _28638 _28639) = (term4 _28638 _28639).
Proof. exact (eq_refl (term3 _28638 _28639)). Qed.
Lemma lem2270399 (_28638 : int) (_28639 : int) : (int_ge _28638 _28639) = (term4 _28638 _28639).
Proof. exact (TRANS (@lem2270397 _28638 _28639) (@lem2270398 _28638 _28639)). Qed.
Lemma lem2270400 (_28638 : int) : term5 _28638.
Proof. exact (fun _28639 : int => @lem2270399 _28638 _28639). Qed.
Lemma lem2270401 : term6.
Proof. exact (fun _28638 : int => @lem2270400 _28638). Qed.
Lemma lem2270402 (_28638 : int) : term7 _28638.
Proof. exact (@lem2270401 _28638). Qed.
Lemma lem2270403 (_28638 : int) : (term7 _28638) = (term5 _28638).
Proof. exact (eq_refl (term7 _28638)). Qed.
Lemma lem2270404 (_28638 : int) : term5 _28638.
Proof. exact (EQ_MP (@lem2270403 _28638) (@lem2270402 _28638)). Qed.
Lemma lem2270405 (_28638 : int) (_28639 : int) : term8 _28638 _28639.
Proof. exact (@lem2270404 _28638 _28639). Qed.
Lemma lem2270406 (_28638 : int) (_28639 : int) : (term8 _28638 _28639) = ((int_ge _28638 _28639) = (term4 _28638 _28639)).
Proof. exact (eq_refl (term8 _28638 _28639)). Qed.
Lemma lem2270407 (_28638 : int) (_28639 : int) : (int_ge _28638 _28639) = (term4 _28638 _28639).
Proof. exact (EQ_MP (@lem2270406 _28638 _28639) (@lem2270405 _28638 _28639)). Qed.
Lemma lem2270450 (x : int) (y : int) : (int_ge x y) = (term4 x y).
Proof. exact (@lem2270407 x y). Qed.
Lemma lem2270451 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2270450 x y). Qed.
Lemma lem2270452 : term6.
Proof. exact (fun x : int => @lem2270451 x). Qed.
