Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21028_term_abbrevs.
Lemma lem21028 (p : Prop) : ((term0 p) = (~ p)) = ((term0 p) = (~ p)).
Proof. exact (eq_refl ((term0 p) = (~ p))). Qed.
