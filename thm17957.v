Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17957_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Lemma lem17952 (t1 : Prop) : term0 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem17953 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem17954 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem17953 t1) (@lem17952 t1)). Qed.
Lemma lem17955 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem17954 t1 t2). Qed.
Lemma lem17956 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem17957 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem17956 t1 t2) (@lem17955 t1 t2)). Qed.
