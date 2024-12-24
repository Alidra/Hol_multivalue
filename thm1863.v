Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1863_term_abbrevs.
Lemma lem1863 {A : Type'} (x : A) : (term0 A x) = ((x = x) = True).
Proof. exact (eq_refl (term0 A x)). Qed.
