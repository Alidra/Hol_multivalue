Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20815_term_abbrevs.
Require Import thm20793_spec.
Lemma lem20803 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20804 (b : Prop) (a : Prop) (h1 : a = True) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20803 b) (@lem20793 a h1)). Qed.
Lemma lem20805 (b : Prop) : (term2 b) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20806 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem20807 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20806 b a) (@lem20805 b)). Qed.
Lemma lem20808 (a : Prop) (b : Prop) : (term1 b a) = ((term6 a b) = (term7 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20810 (a : Prop) (b : Prop) : (term5 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem20809) (@lem20808 a b)). Qed.
Lemma lem20811 (b : Prop) : ((term3 b) = (term4 b)) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl ((term3 b) = (term4 b))). Qed.
Lemma lem20812 (a : Prop) (b : Prop) : ((term1 b a) = ((term3 b) = (term4 b))) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20810 a b) (@lem20811 b)). Qed.
Lemma lem20813 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (TRANS (@lem20807 a b) (@lem20812 a b)). Qed.
Lemma lem20814 (b : Prop) (a : Prop) (h1 : a = True) : ((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b)).
Proof. exact (EQ_MP (@lem20813 a b) (@lem20804 b a h1)). Qed.
Lemma lem20815 (b : Prop) (a : Prop) (h1 : a = True) : ((term3 b) = (term4 b)) = ((term6 a b) = (term7 a b)).
Proof. exact (SYM (@lem20814 b a h1)). Qed.
