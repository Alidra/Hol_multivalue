Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982785_term_abbrevs.
Require Import REAL_POLY_NEG_CLAUSES_spec.
Lemma lem1982782 : term0.
Proof. exact (proj1 (@lem1384312)). Qed.
Lemma lem1982783 (x : real) : term1 x.
Proof. exact (@lem1982782 x). Qed.
Lemma lem1982784 (x : real) : (term1 x) = ((real_neg x) = (term2 x)).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1982785 (x : real) : (real_neg x) = (term2 x).
Proof. exact (EQ_MP (@lem1982784 x) (@lem1982783 x)). Qed.