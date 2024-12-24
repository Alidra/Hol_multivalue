Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400772_term_abbrevs.
Require Import NOT_IN_EMPTY_spec.
Lemma lem5400770 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5400771 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5400772 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5400771 A x) (@lem5400770 A x)). Qed.
