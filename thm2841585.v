Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841585_term_abbrevs.
Require Import int_add_th_spec.
Lemma lem2841582 (x : int) : term0 x.
Proof. exact (@lem2284714 x). Qed.
Lemma lem2841583 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841584 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841583 x) (@lem2841582 x)). Qed.
Lemma lem2841585 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841584 x y). Qed.
