Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21420_term_abbrevs.
Require Import thm21398_spec.
Lemma lem21408 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem21409 (b : Prop) (a : Prop) (h1 : a = True) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem21408 b) (@lem21398 a h1)). Qed.
Lemma lem21410 (b : Prop) : (term2 b) = ((True -> b) = (term3 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21411 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem21412 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((True -> b) = (term3 b))).
Proof. exact (MK_COMB (@lem21411 b a) (@lem21410 b)). Qed.
Lemma lem21413 (a : Prop) (b : Prop) : (term1 b a) = ((a -> b) = (term5 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem21414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21415 (a : Prop) (b : Prop) : (term4 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem21414) (@lem21413 a b)). Qed.
Lemma lem21416 (b : Prop) : ((True -> b) = (term3 b)) = ((True -> b) = (term3 b)).
Proof. exact (eq_refl ((True -> b) = (term3 b))). Qed.
Lemma lem21417 (a : Prop) (b : Prop) : ((term1 b a) = ((True -> b) = (term3 b))) = (((a -> b) = (term5 a b)) = ((True -> b) = (term3 b))).
Proof. exact (MK_COMB (@lem21415 a b) (@lem21416 b)). Qed.
Lemma lem21418 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((a -> b) = (term5 a b)) = ((True -> b) = (term3 b))).
Proof. exact (TRANS (@lem21412 a b) (@lem21417 a b)). Qed.
Lemma lem21419 (b : Prop) (a : Prop) (h1 : a = True) : ((a -> b) = (term5 a b)) = ((True -> b) = (term3 b)).
Proof. exact (EQ_MP (@lem21418 a b) (@lem21409 b a h1)). Qed.
Lemma lem21420 (b : Prop) (a : Prop) (h1 : a = True) : ((True -> b) = (term3 b)) = ((a -> b) = (term5 a b)).
Proof. exact (SYM (@lem21419 b a h1)). Qed.
