Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299888_term_abbrevs.
Require Import thm2299838_spec.
Lemma lem2299885 (x : int) : term0 x.
Proof. exact (@lem2299838 x). Qed.
Lemma lem2299886 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299887 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299886 x) (@lem2299885 x)). Qed.
Lemma lem2299888 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299887 x y). Qed.
