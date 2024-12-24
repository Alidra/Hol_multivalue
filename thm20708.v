Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20708_term_abbrevs.
Require Import thm20686_spec.
Lemma lem20696 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20697 (b : Prop) (a : Prop) (h1 : a = True) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem20696 b) (@lem20686 a h1)). Qed.
Lemma lem20698 (b : Prop) : (term2 b) = ((True \/ b) = (term3 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem20699 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem20700 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((True \/ b) = (term3 b))).
Proof. exact (MK_COMB (@lem20699 b a) (@lem20698 b)). Qed.
Lemma lem20701 (b : Prop) (a : Prop) : (term1 b a) = ((a \/ b) = (term5 b a)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem20702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20703 (b : Prop) (a : Prop) : (term4 b a) = (term6 b a).
Proof. exact (MK_COMB (@lem20702) (@lem20701 b a)). Qed.
Lemma lem20704 (b : Prop) : ((True \/ b) = (term3 b)) = ((True \/ b) = (term3 b)).
Proof. exact (eq_refl ((True \/ b) = (term3 b))). Qed.
Lemma lem20705 (a : Prop) (b : Prop) : ((term1 b a) = ((True \/ b) = (term3 b))) = (((a \/ b) = (term5 b a)) = ((True \/ b) = (term3 b))).
Proof. exact (MK_COMB (@lem20703 b a) (@lem20704 b)). Qed.
Lemma lem20706 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((a \/ b) = (term5 b a)) = ((True \/ b) = (term3 b))).
Proof. exact (TRANS (@lem20700 a b) (@lem20705 a b)). Qed.
Lemma lem20707 (b : Prop) (a : Prop) (h1 : a = True) : ((a \/ b) = (term5 b a)) = ((True \/ b) = (term3 b)).
Proof. exact (EQ_MP (@lem20706 a b) (@lem20697 b a h1)). Qed.
Lemma lem20708 (b : Prop) (a : Prop) (h1 : a = True) : ((True \/ b) = (term3 b)) = ((a \/ b) = (term5 b a)).
Proof. exact (SYM (@lem20707 b a h1)). Qed.
