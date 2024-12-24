Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21529_term_abbrevs.
Require Import thm21505_spec.
Lemma lem21517 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem21518 (b : Prop) (a : Prop) (h1 : a = True) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem21517 b) (@lem21505 a h1)). Qed.
Lemma lem21519 (b : Prop) : (term2 b) = (term3 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21520 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem21521 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = (term3 b)).
Proof. exact (MK_COMB (@lem21520 b a) (@lem21519 b)). Qed.
Lemma lem21522 (b : Prop) (a : Prop) : (term1 b a) = (term5 b a).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem21523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21524 (b : Prop) (a : Prop) : (term4 b a) = (term6 b a).
Proof. exact (MK_COMB (@lem21523) (@lem21522 b a)). Qed.
Lemma lem21525 (b : Prop) : (term3 b) = (term3 b).
Proof. exact (eq_refl (term3 b)). Qed.
Lemma lem21526 (a : Prop) (b : Prop) : ((term1 b a) = (term3 b)) = ((term5 b a) = (term3 b)).
Proof. exact (MK_COMB (@lem21524 b a) (@lem21525 b)). Qed.
Lemma lem21527 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term5 b a) = (term3 b)).
Proof. exact (TRANS (@lem21521 a b) (@lem21526 a b)). Qed.
Lemma lem21528 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b a) = (term3 b).
Proof. exact (EQ_MP (@lem21527 a b) (@lem21518 b a h1)). Qed.
Lemma lem21529 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b) = (term5 b a).
Proof. exact (SYM (@lem21528 b a h1)). Qed.
