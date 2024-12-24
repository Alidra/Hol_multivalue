Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211729_term_abbrevs.
Require Import NOT_IN_EMPTY_spec.
Lemma lem3211727 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3211728 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3211729 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3211728 A x) (@lem3211727 A x)). Qed.
