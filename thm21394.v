Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21394_term_abbrevs.
Lemma lem21394 (a : Prop) (b : Prop) : ((a -> b) = (term0 a b)) = ((a -> b) = (term0 a b)).
Proof. exact (eq_refl ((a -> b) = (term0 a b))). Qed.
