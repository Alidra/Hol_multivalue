Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm12653_term_abbrevs.
Require Import COND_CLAUSES_spec.
Lemma lem12648 {A : Type'} (t1 : A) : term0 A t1.
Proof. exact (@lem12647 A t1). Qed.
Lemma lem12649 {A : Type'} (t1 : A) : (term0 A t1) = (term1 A t1).
Proof. exact (eq_refl (term0 A t1)). Qed.
Lemma lem12650 {A : Type'} (t1 : A) : term1 A t1.
Proof. exact (EQ_MP (@lem12649 A t1) (@lem12648 A t1)). Qed.
Lemma lem12651 {A : Type'} (t1 : A) (t2 : A) : term2 A t1 t2.
Proof. exact (@lem12650 A t1 t2). Qed.
Lemma lem12652 {A : Type'} (t1 : A) (t2 : A) : (term2 A t1 t2) = (term3 A t1 t2).
Proof. exact (eq_refl (term2 A t1 t2)). Qed.
Lemma lem12653 {A : Type'} (t1 : A) (t2 : A) : term3 A t1 t2.
Proof. exact (EQ_MP (@lem12652 A t1 t2) (@lem12651 A t1 t2)). Qed.
