Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982792_term_abbrevs.
Require Import REAL_POLY_NEG_CLAUSES_spec.
Lemma lem1982786 : term0.
Proof. exact (proj2 (@lem1384312)). Qed.
Lemma lem1982787 (x : real) : term1 x.
Proof. exact (@lem1982786 x). Qed.
Lemma lem1982788 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1982789 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1982788 x) (@lem1982787 x)). Qed.
Lemma lem1982790 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1982789 x y). Qed.
Lemma lem1982791 (x : real) (y : real) : (term3 x y) = ((real_sub x y) = (term4 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1982792 (x : real) (y : real) : (real_sub x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1982791 x y) (@lem1982790 x y)). Qed.
