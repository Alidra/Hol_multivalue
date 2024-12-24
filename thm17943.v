Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17943_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Lemma lem17937 (t1 : Prop) : term0 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem17938 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem17939 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem17938 t1) (@lem17937 t1)). Qed.
Lemma lem17940 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem17939 t1 t2). Qed.
Lemma lem17941 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem17942 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem17941 t1 t2) (@lem17940 t1 t2)). Qed.
Lemma lem17943 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem17942 t1 t2 t3). Qed.
