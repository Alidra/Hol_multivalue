Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20943_term_abbrevs.
Require Import thm20909_spec.
Lemma lem20931 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20932 (b : Prop) (a : Prop) (h1 : a = False) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20931 b) (@lem20909 a h1)). Qed.
Lemma lem20933 (b : Prop) : (term2 b) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20934 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem20935 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20934 b a) (@lem20933 b)). Qed.
Lemma lem20936 (a : Prop) (b : Prop) : (term1 b a) = ((term6 a b) = (term7 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20938 (a : Prop) (b : Prop) : (term5 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem20937) (@lem20936 a b)). Qed.
Lemma lem20939 (b : Prop) : ((term3 b) = (term4 b)) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl ((term3 b) = (term4 b))). Qed.
Lemma lem20940 (a : Prop) (b : Prop) : ((term1 b a) = ((term3 b) = (term4 b))) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20938 a b) (@lem20939 b)). Qed.
Lemma lem20941 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (TRANS (@lem20935 a b) (@lem20940 a b)). Qed.
Lemma lem20942 (b : Prop) (a : Prop) (h1 : a = False) : ((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b)).
Proof. exact (EQ_MP (@lem20941 a b) (@lem20932 b a h1)). Qed.
Lemma lem20943 (b : Prop) (a : Prop) (h1 : a = False) : ((term3 b) = (term4 b)) = ((term6 a b) = (term7 a b)).
Proof. exact (SYM (@lem20942 b a h1)). Qed.
