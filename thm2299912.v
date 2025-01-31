Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299912_term_abbrevs.
Require Import thm2299776_spec.
Lemma lem2299909 (x : int) : term0 x.
Proof. exact (@lem2299776 x). Qed.
Lemma lem2299910 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299911 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299910 x) (@lem2299909 x)). Qed.
Lemma lem2299912 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299911 x y). Qed.
