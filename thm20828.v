Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20828_term_abbrevs.
Require Import thm20794_spec.
Lemma lem20816 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20817 (b : Prop) (a : Prop) (h1 : a = False) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20816 b) (@lem20794 a h1)). Qed.
Lemma lem20818 (b : Prop) : (term2 b) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20819 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem20820 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20819 b a) (@lem20818 b)). Qed.
Lemma lem20821 (a : Prop) (b : Prop) : (term1 b a) = ((term6 a b) = (term7 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20823 (a : Prop) (b : Prop) : (term5 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem20822) (@lem20821 a b)). Qed.
Lemma lem20824 (b : Prop) : ((term3 b) = (term4 b)) = ((term3 b) = (term4 b)).
Proof. exact (eq_refl ((term3 b) = (term4 b))). Qed.
Lemma lem20825 (a : Prop) (b : Prop) : ((term1 b a) = ((term3 b) = (term4 b))) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (MK_COMB (@lem20823 a b) (@lem20824 b)). Qed.
Lemma lem20826 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b))).
Proof. exact (TRANS (@lem20820 a b) (@lem20825 a b)). Qed.
Lemma lem20827 (b : Prop) (a : Prop) (h1 : a = False) : ((term6 a b) = (term7 a b)) = ((term3 b) = (term4 b)).
Proof. exact (EQ_MP (@lem20826 a b) (@lem20817 b a h1)). Qed.
Lemma lem20828 (b : Prop) (a : Prop) (h1 : a = False) : ((term3 b) = (term4 b)) = ((term6 a b) = (term7 a b)).
Proof. exact (SYM (@lem20827 b a h1)). Qed.
