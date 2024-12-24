Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import tybit1_INDUCT_term_abbrevs.
Require Import thm7929851_spec.
Require Import thm7931296_spec.
Lemma lem7931297 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7931298 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (MK_COMB (@lem7931297 A) (@lem7931296 A)). Qed.
Lemma lem7931299 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem7931300 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7931301 {A : Type'} : ((term1 A) = (term2 A)) = ((term1 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7931300 A) (@lem7931299 A)). Qed.
Lemma lem7931302 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7931303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7931304 {A : Type'} : (term4 A) = (term6 A).
Proof. exact (MK_COMB (@lem7931303) (@lem7931302 A)). Qed.
Lemma lem7931305 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7931306 {A : Type'} : ((term1 A) = (term3 A)) = ((term5 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7931304 A) (@lem7931305 A)). Qed.
Lemma lem7931307 {A : Type'} : ((term1 A) = (term2 A)) = ((term5 A) = (term3 A)).
Proof. exact (TRANS (@lem7931301 A) (@lem7931306 A)). Qed.
Lemma lem7931308 {A : Type'} : (term5 A) = (term3 A).
Proof. exact (EQ_MP (@lem7931307 A) (@lem7931298 A)). Qed.
Lemma lem7931309 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem7931308 A) (@lem7929851 A)). Qed.
