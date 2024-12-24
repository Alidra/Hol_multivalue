Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9524_term_abbrevs.
Lemma lem9524 {A : Type'} (x : A) : (term0 A x) = ((term1 A x) = x).
Proof. exact (eq_refl (term0 A x)). Qed.
