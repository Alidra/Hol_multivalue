Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406287_term_abbrevs.
Require Import INT_SUB_spec.
Lemma lem2406284 (x : int) : term0 x.
Proof. exact (@lem2319812 x). Qed.
Lemma lem2406285 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2406286 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2406285 x) (@lem2406284 x)). Qed.
Lemma lem2406287 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2406286 x y). Qed.
