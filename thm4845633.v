Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4845633_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Lemma lem4845624 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4845625 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4845626 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4845625 t1) (@lem4845624 t1)). Qed.
Lemma lem4845627 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4845626 t1 t2). Qed.
Lemma lem4845628 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4845629 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4845628 t1 t2) (@lem4845627 t1 t2)). Qed.
Lemma lem4845630 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4845629 t1 t2 t3). Qed.
Lemma lem4845631 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4845632 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4845631 t1 t2 t3) (@lem4845630 t1 t2 t3)). Qed.
Lemma lem4845633 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4845632 t1 t2 t3)). Qed.
