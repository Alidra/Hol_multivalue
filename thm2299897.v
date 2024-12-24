Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299897_term_abbrevs.
Require Import thm2299814_spec.
Lemma lem2299894 (x : int) : term0 x.
Proof. exact (@lem2299814 x). Qed.
Lemma lem2299895 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299896 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299895 x) (@lem2299894 x)). Qed.
Lemma lem2299897 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299896 x y). Qed.
