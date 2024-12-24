Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458986_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Lemma lem3458977 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3458978 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3458979 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3458978 t1) (@lem3458977 t1)). Qed.
Lemma lem3458980 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3458979 t1 t2). Qed.
Lemma lem3458981 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3458982 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3458981 t1 t2) (@lem3458980 t1 t2)). Qed.
Lemma lem3458983 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3458982 t1 t2 t3). Qed.
Lemma lem3458984 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3458985 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3458984 t1 t2 t3) (@lem3458983 t1 t2 t3)). Qed.
Lemma lem3458986 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3458985 t1 t2 t3)). Qed.
