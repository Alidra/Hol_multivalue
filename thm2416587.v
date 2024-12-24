Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416587_term_abbrevs.
Require Import thm2416504_spec.
Lemma lem2416584 : term0.
Proof. exact (proj1 (@lem2416504)). Qed.
Lemma lem2416585 (x : int) : term1 x.
Proof. exact (@lem2416584 x). Qed.
Lemma lem2416586 (x : int) : (term1 x) = ((int_neg x) = (term2 x)).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2416587 (x : int) : (int_neg x) = (term2 x).
Proof. exact (EQ_MP (@lem2416586 x) (@lem2416585 x)). Qed.
