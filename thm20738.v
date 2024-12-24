Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20738_term_abbrevs.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1855_spec.
Lemma lem20725 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem20726 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem20725 b). Qed.
Lemma lem20727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20728 (b : Prop) : (term0 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem20727) (@lem20726 b)). Qed.
Lemma lem20730 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem20731 (b : Prop) : (term1 b) = True.
Proof. exact (@lem20730 (~ b)). Qed.
Lemma lem20732 (b : Prop) : ((True \/ b) = (term1 b)) = (True = True).
Proof. exact (MK_COMB (@lem20728 b) (@lem20731 b)). Qed.
Lemma lem20734 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem20735 : (True = True) = True.
Proof. exact (@lem20734 True). Qed.
Lemma lem20736 (b : Prop) : ((True \/ b) = (term1 b)) = True.
Proof. exact (TRANS (@lem20732 b) (@lem20735)). Qed.
Lemma lem20737 (b : Prop) : True = ((True \/ b) = (term1 b)).
Proof. exact (SYM (@lem20736 b)). Qed.
Lemma lem20738 (b : Prop) : (True \/ b) = (term1 b).
Proof. exact (EQ_MP (@lem20737 b) (@lem0)). Qed.
