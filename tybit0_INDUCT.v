Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import tybit0_INDUCT_term_abbrevs.
Require Import thm7926528_spec.
Require Import thm7927969_spec.
Lemma lem7927970 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7927971 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (MK_COMB (@lem7927970 A) (@lem7927969 A)). Qed.
Lemma lem7927972 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem7927973 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7927974 {A : Type'} : ((term1 A) = (term2 A)) = ((term1 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7927973 A) (@lem7927972 A)). Qed.
Lemma lem7927975 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7927976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7927977 {A : Type'} : (term4 A) = (term6 A).
Proof. exact (MK_COMB (@lem7927976) (@lem7927975 A)). Qed.
Lemma lem7927978 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7927979 {A : Type'} : ((term1 A) = (term3 A)) = ((term5 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7927977 A) (@lem7927978 A)). Qed.
Lemma lem7927980 {A : Type'} : ((term1 A) = (term2 A)) = ((term5 A) = (term3 A)).
Proof. exact (TRANS (@lem7927974 A) (@lem7927979 A)). Qed.
Lemma lem7927981 {A : Type'} : (term5 A) = (term3 A).
Proof. exact (EQ_MP (@lem7927980 A) (@lem7927971 A)). Qed.
Lemma lem7927982 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem7927981 A) (@lem7926528 A)). Qed.
