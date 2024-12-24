Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299948_term_abbrevs.
Require Import thm2299686_spec.
Lemma lem2299945 (x : int) : term0 x.
Proof. exact (@lem2299686 x). Qed.
Lemma lem2299946 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299947 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299946 x) (@lem2299945 x)). Qed.
Lemma lem2299948 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2299947 x y). Qed.
