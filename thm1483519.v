Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483519_term_abbrevs.
Require Import REAL_POLY_NEG_CLAUSES_spec.
Lemma lem1483513 : term0.
Proof. exact (proj2 (@lem1384312)). Qed.
Lemma lem1483514 (x : real) : term1 x.
Proof. exact (@lem1483513 x). Qed.
Lemma lem1483515 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1483516 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1483515 x) (@lem1483514 x)). Qed.
Lemma lem1483517 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1483516 x y). Qed.
Lemma lem1483518 (x : real) (y : real) : (term3 x y) = ((real_sub x y) = (term4 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1483519 (x : real) (y : real) : (real_sub x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1483518 x y) (@lem1483517 x y)). Qed.
