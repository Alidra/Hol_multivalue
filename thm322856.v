Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm322856_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Lemma lem322847 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem322848 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem322849 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem322848 t1) (@lem322847 t1)). Qed.
Lemma lem322850 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem322849 t1 t2). Qed.
Lemma lem322851 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem322852 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem322851 t1 t2) (@lem322850 t1 t2)). Qed.
Lemma lem322853 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem322852 t1 t2 t3). Qed.
Lemma lem322854 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem322855 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem322854 t1 t2 t3) (@lem322853 t1 t2 t3)). Qed.
Lemma lem322856 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem322855 t1 t2 t3)). Qed.
