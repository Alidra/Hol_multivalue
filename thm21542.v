Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21542_term_abbrevs.
Require Import thm21506_spec.
Lemma lem21530 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem21531 (b : Prop) (a : Prop) (h1 : a = False) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem21530 b) (@lem21506 a h1)). Qed.
Lemma lem21532 (b : Prop) : (term2 b) = (term3 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21533 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem21534 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = (term3 b)).
Proof. exact (MK_COMB (@lem21533 b a) (@lem21532 b)). Qed.
Lemma lem21535 (b : Prop) (a : Prop) : (term1 b a) = (term5 b a).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem21536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21537 (b : Prop) (a : Prop) : (term4 b a) = (term6 b a).
Proof. exact (MK_COMB (@lem21536) (@lem21535 b a)). Qed.
Lemma lem21538 (b : Prop) : (term3 b) = (term3 b).
Proof. exact (eq_refl (term3 b)). Qed.
Lemma lem21539 (a : Prop) (b : Prop) : ((term1 b a) = (term3 b)) = ((term5 b a) = (term3 b)).
Proof. exact (MK_COMB (@lem21537 b a) (@lem21538 b)). Qed.
Lemma lem21540 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term5 b a) = (term3 b)).
Proof. exact (TRANS (@lem21534 a b) (@lem21539 a b)). Qed.
Lemma lem21541 (b : Prop) (a : Prop) (h1 : a = False) : (term5 b a) = (term3 b).
Proof. exact (EQ_MP (@lem21540 a b) (@lem21531 b a h1)). Qed.
Lemma lem21542 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b) = (term5 b a).
Proof. exact (SYM (@lem21541 b a h1)). Qed.
