Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm310010_term_abbrevs.
Require Import NOT_IMP_spec.
Lemma lem310007 (t1 : Prop) : term0 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem310008 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem310009 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem310008 t1) (@lem310007 t1)). Qed.
Lemma lem310010 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem310009 t1 t2). Qed.
