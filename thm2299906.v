Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299906_term_abbrevs.
Require Import thm2299790_spec.
Lemma lem2299903 (x : int) : term0 x.
Proof. exact (@lem2299790 x). Qed.
Lemma lem2299904 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299905 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299904 x) (@lem2299903 x)). Qed.
Lemma lem2299906 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299905 x y). Qed.
