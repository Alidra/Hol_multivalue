Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1995456_term_abbrevs.
Require Import real_div_spec.
Lemma lem1995453 (x : real) : term0 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1995454 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1995455 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1995454 x) (@lem1995453 x)). Qed.
Lemma lem1995456 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1995455 x y). Qed.
