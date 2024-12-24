Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318532_term_abbrevs.
Require Import int_mul_th_spec.
Lemma lem2318529 (x : int) : term0 x.
Proof. exact (@lem2287415 x). Qed.
Lemma lem2318530 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318531 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318530 x) (@lem2318529 x)). Qed.
Lemma lem2318532 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318531 x y). Qed.
