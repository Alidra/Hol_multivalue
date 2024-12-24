Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318574_term_abbrevs.
Require Import int_eq_spec.
Lemma lem2318571 (x : int) : term0 x.
Proof. exact (@lem2268427 x). Qed.
Lemma lem2318572 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318573 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318572 x) (@lem2318571 x)). Qed.
Lemma lem2318574 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318573 x y). Qed.
