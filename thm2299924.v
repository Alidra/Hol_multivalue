Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299924_term_abbrevs.
Require Import thm2299742_spec.
Lemma lem2299921 (x : int) : term0 x.
Proof. exact (@lem2299742 x). Qed.
Lemma lem2299922 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299923 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299922 x) (@lem2299921 x)). Qed.
Lemma lem2299924 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299923 x y). Qed.
