Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1809_term_abbrevs.
Require Import BETA_THM_spec.
Lemma lem1806 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1807 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1808 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1807 A B f) (@lem1806 A B f)). Qed.
Lemma lem1809 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1808 A B f y). Qed.
