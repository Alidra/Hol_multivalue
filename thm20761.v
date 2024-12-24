Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20761_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20721_spec.
Lemma lem20742 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem20743 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem20742 b). Qed.
Lemma lem20744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20745 (b : Prop) : (term0 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem20744) (@lem20743 b)). Qed.
Lemma lem20747 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem20748 (b : Prop) : (term1 b) = (term2 b).
Proof. exact (@lem20747 (~ b)). Qed.
Lemma lem20750 (t : Prop) : (term2 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem20751 (b : Prop) : (term2 b) = b.
Proof. exact (@lem20750 b). Qed.
Lemma lem20752 (b : Prop) : (term1 b) = b.
Proof. exact (TRANS (@lem20748 b) (@lem20751 b)). Qed.
Lemma lem20753 (b : Prop) : ((False \/ b) = (term1 b)) = (b = b).
Proof. exact (MK_COMB (@lem20745 b) (@lem20752 b)). Qed.
Lemma lem20755 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20756 (x : Prop) : (x = x) = True.
Proof. exact (@lem20755 Prop x). Qed.
Lemma lem20757 (b : Prop) : (b = b) = True.
Proof. exact (@lem20756 b). Qed.
Lemma lem20758 (b : Prop) : ((False \/ b) = (term1 b)) = True.
Proof. exact (TRANS (@lem20753 b) (@lem20757 b)). Qed.
Lemma lem20759 (b : Prop) : True = ((False \/ b) = (term1 b)).
Proof. exact (SYM (@lem20758 b)). Qed.
Lemma lem20760 (b : Prop) : (False \/ b) = (term1 b).
Proof. exact (EQ_MP (@lem20759 b) (@lem0)). Qed.
Lemma lem20761 (b : Prop) (a : Prop) (h1 : a = False) : (a \/ b) = (term3 b a).
Proof. exact (EQ_MP (@lem20721 b a h1) (@lem20760 b)). Qed.
