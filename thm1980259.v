Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980259_term_abbrevs.
Require Import real_ge_spec.
Lemma lem1980256 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1980257 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1980258 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1980257 y) (@lem1980256 y)). Qed.
Lemma lem1980259 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1980258 y x). Qed.
