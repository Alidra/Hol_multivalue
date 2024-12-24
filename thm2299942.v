Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299942_term_abbrevs.
Require Import thm2299700_spec.
Lemma lem2299939 (x : int) : term0 x.
Proof. exact (@lem2299700 x). Qed.
Lemma lem2299940 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299941 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299940 x) (@lem2299939 x)). Qed.
Lemma lem2299942 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299941 x y). Qed.
