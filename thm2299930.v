Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299930_term_abbrevs.
Require Import thm2299728_spec.
Lemma lem2299927 (x : int) : term0 x.
Proof. exact (@lem2299728 x). Qed.
Lemma lem2299928 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299929 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299928 x) (@lem2299927 x)). Qed.
Lemma lem2299930 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299929 x y). Qed.
