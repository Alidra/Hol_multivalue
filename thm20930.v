Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20930_term_abbrevs.
Require Import thm20908_spec.
Lemma lem20918 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20919 (b : Prop) (a : Prop) (h1 : a = True) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20918 b) (@lem20908 a h1)). Qed.
Lemma lem20920 (b : Prop) : (term2 b) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20921 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem20922 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20921 b a) (@lem20920 b)). Qed.
Lemma lem20923 (a : Prop) (b : Prop) : (term1 b a) = ((term6 a b) = (term7 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20925 (a : Prop) (b : Prop) : (term5 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem20924) (@lem20923 a b)). Qed.
Lemma lem20926 (b : Prop) : ((term3 b) = (term4 b)) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl ((term3 b) = (term4 b))). Qed.
Lemma lem20927 (a : Prop) (b : Prop) : ((term1 b a) = ((term3 b) = (term4 b))) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20925 a b) (@lem20926 b)). Qed.
Lemma lem20928 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (TRANS (@lem20922 a b) (@lem20927 a b)). Qed.
Lemma lem20929 (b : Prop) (a : Prop) (h1 : a = True) : ((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b)).
Proof. exact (EQ_MP (@lem20928 a b) (@lem20919 b a h1)). Qed.
Lemma lem20930 (b : Prop) (a : Prop) (h1 : a = True) : ((term3 b) = (term4 b)) = ((term6 a b) = (term7 a b)).
Proof. exact (SYM (@lem20929 b a h1)). Qed.
