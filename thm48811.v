Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48811_term_abbrevs.
Require Import GEQ_DEF_spec.
Lemma lem48808 {A : Type'} (a : A) : term0 A a.
Proof. exact (@lem44156 A a). Qed.
Lemma lem48809 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem48810 {A : Type'} (a : A) : term1 A a.
Proof. exact (EQ_MP (@lem48809 A a) (@lem48808 A a)). Qed.
Lemma lem48811 {A : Type'} (a : A) (b : A) : term2 A a b.
Proof. exact (@lem48810 A a b). Qed.
