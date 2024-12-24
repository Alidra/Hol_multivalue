Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980265_term_abbrevs.
Require Import real_gt_spec.
Lemma lem1980262 (y : real) : term0 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1980263 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1980264 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1980263 y) (@lem1980262 y)). Qed.
Lemma lem1980265 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1980264 y x). Qed.
