Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299936_term_abbrevs.
Require Import thm2299714_spec.
Lemma lem2299933 (x : int) : term0 x.
Proof. exact (@lem2299714 x). Qed.
Lemma lem2299934 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299935 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299934 x) (@lem2299933 x)). Qed.
Lemma lem2299936 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299935 x y). Qed.
