Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48214_term_abbrevs.
Lemma lem48214 {A B : Type'} (x : A) (y : B) : (term0 A B x y) = ((term1 A B x y) = y).
Proof. exact (eq_refl (term0 A B x y)). Qed.
