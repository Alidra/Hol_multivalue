Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GT_term_abbrevs.
Lemma lem90402 : Peano.gt = term0.
Proof. exact (@gt_def). Qed.
Lemma lem90403 (_2261 : nat) : _2261 = _2261.
Proof. exact (eq_refl _2261). Qed.
Lemma lem90404 (_2261 : nat) : (Peano.gt _2261) = (term1 _2261).
Proof. exact (MK_COMB (@lem90402) (@lem90403 _2261)). Qed.
Lemma lem90405 (_2261 : nat) : (term1 _2261) = (term2 _2261).
Proof. exact (eq_refl (term1 _2261)). Qed.
Lemma lem90406 (_2261 : nat) : (Peano.gt _2261) = (term2 _2261).
Proof. exact (TRANS (@lem90404 _2261) (@lem90405 _2261)). Qed.
Lemma lem90407 (_2262 : nat) : _2262 = _2262.
Proof. exact (eq_refl _2262). Qed.
Lemma lem90408 (_2261 : nat) (_2262 : nat) : (Peano.gt _2261 _2262) = (term3 _2261 _2262).
Proof. exact (MK_COMB (@lem90406 _2261) (@lem90407 _2262)). Qed.
Lemma lem90409 (_2262 : nat) (_2261 : nat) : (term3 _2261 _2262) = (Peano.lt _2262 _2261).
Proof. exact (eq_refl (term3 _2261 _2262)). Qed.
Lemma lem90410 (_2262 : nat) (_2261 : nat) : (Peano.gt _2261 _2262) = (Peano.lt _2262 _2261).
Proof. exact (TRANS (@lem90408 _2261 _2262) (@lem90409 _2262 _2261)). Qed.
Lemma lem90411 (_2261 : nat) : term4 _2261.
Proof. exact (fun _2262 : nat => @lem90410 _2262 _2261). Qed.
Lemma lem90412 : term5.
Proof. exact (fun _2261 : nat => @lem90411 _2261). Qed.
Lemma lem90413 (_2261 : nat) : term6 _2261.
Proof. exact (@lem90412 _2261). Qed.
Lemma lem90414 (_2261 : nat) : (term6 _2261) = (term4 _2261).
Proof. exact (eq_refl (term6 _2261)). Qed.
Lemma lem90415 (_2261 : nat) : term4 _2261.
Proof. exact (EQ_MP (@lem90414 _2261) (@lem90413 _2261)). Qed.
Lemma lem90416 (_2261 : nat) (_2262 : nat) : term7 _2261 _2262.
Proof. exact (@lem90415 _2261 _2262). Qed.
Lemma lem90417 (_2262 : nat) (_2261 : nat) : (term7 _2261 _2262) = ((Peano.gt _2261 _2262) = (Peano.lt _2262 _2261)).
Proof. exact (eq_refl (term7 _2261 _2262)). Qed.
Lemma lem90418 (_2262 : nat) (_2261 : nat) : (Peano.gt _2261 _2262) = (Peano.lt _2262 _2261).
Proof. exact (EQ_MP (@lem90417 _2262 _2261) (@lem90416 _2261 _2262)). Qed.
Lemma lem90461 (n : nat) (m : nat) : (Peano.gt m n) = (Peano.lt n m).
Proof. exact (@lem90418 n m). Qed.
Lemma lem90462 (n : nat) : term8 n.
Proof. exact (fun m : nat => @lem90461 n m). Qed.
Lemma lem90463 : term9.
Proof. exact (fun n : nat => @lem90462 n). Qed.
