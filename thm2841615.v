Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841615_term_abbrevs.
Require Import int_le_spec.
Lemma lem2841612 (x : int) : term0 x.
Proof. exact (@lem2269094 x). Qed.
Lemma lem2841613 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841614 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841613 x) (@lem2841612 x)). Qed.
Lemma lem2841615 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841614 x y). Qed.
