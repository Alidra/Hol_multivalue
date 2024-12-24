Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20721_term_abbrevs.
Require Import thm20687_spec.
Lemma lem20709 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20710 (b : Prop) (a : Prop) (h1 : a = False) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20709 b) (@lem20687 a h1)). Qed.
Lemma lem20711 (b : Prop) : (term2 b) = ((False \/ b) = (term3 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20712 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem20713 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((False \/ b) = (term3 b))).
Proof. exact (MK_COMB (@lem20712 b a) (@lem20711 b)). Qed.
Lemma lem20714 (b : Prop) (a : Prop) : (term1 b a) = ((a \/ b) = (term5 b a)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20716 (b : Prop) (a : Prop) : (term4 b a) = (term6 b a).
Proof. exact (MK_COMB (@lem20715) (@lem20714 b a)). Qed.
Lemma lem20717 (b : Prop) : ((False \/ b) = (term3 b)) = ((False \/ b) = (term3 b)).
Proof. exact (eq_refl ((False \/ b) = (term3 b))). Qed.
Lemma lem20718 (a : Prop) (b : Prop) : ((term1 b a) = ((False \/ b) = (term3 b))) = (((a \/ b) = (term5 b a)) = ((False \/ b) = (term3 b))).
Proof. exact (MK_COMB (@lem20716 b a) (@lem20717 b)). Qed.
Lemma lem20719 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((a \/ b) = (term5 b a)) = ((False \/ b) = (term3 b))).
Proof. exact (TRANS (@lem20713 a b) (@lem20718 a b)). Qed.
Lemma lem20720 (b : Prop) (a : Prop) (h1 : a = False) : ((a \/ b) = (term5 b a)) = ((False \/ b) = (term3 b)).
Proof. exact (EQ_MP (@lem20719 a b) (@lem20710 b a h1)). Qed.
Lemma lem20721 (b : Prop) (a : Prop) (h1 : a = False) : ((False \/ b) = (term3 b)) = ((a \/ b) = (term5 b a)).
Proof. exact (SYM (@lem20720 b a h1)). Qed.
