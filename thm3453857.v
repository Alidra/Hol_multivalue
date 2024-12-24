Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453857_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Lemma lem3453848 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3453849 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3453850 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3453849 t1) (@lem3453848 t1)). Qed.
Lemma lem3453851 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3453850 t1 t2). Qed.
Lemma lem3453852 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3453853 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3453852 t1 t2) (@lem3453851 t1 t2)). Qed.
Lemma lem3453854 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3453853 t1 t2 t3). Qed.
Lemma lem3453855 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3453856 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3453855 t1 t2 t3) (@lem3453854 t1 t2 t3)). Qed.
Lemma lem3453857 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3453856 t1 t2 t3)). Qed.
