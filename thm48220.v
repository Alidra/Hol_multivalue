Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48220_term_abbrevs.
Lemma lem48220 {A B : Type'} (y : B) (x : A) : (term0 A B x y) = ((term1 A B x y) = x).
Proof. exact (eq_refl (term0 A B x y)). Qed.
