Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299882_term_abbrevs.
Require Import thm2299852_spec.
Lemma lem2299879 (x : int) : term0 x.
Proof. exact (@lem2299852 x). Qed.
Lemma lem2299880 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299881 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299880 x) (@lem2299879 x)). Qed.
Lemma lem2299882 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299881 x y). Qed.
