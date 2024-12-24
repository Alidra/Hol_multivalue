Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17934_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Lemma lem17931 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem17932 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem17933 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem17932 A x) (@lem17931 A x)). Qed.
Lemma lem17934 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem17933 A x y). Qed.
