Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302581_term_abbrevs.
Lemma lem302581 (m : nat) : (term0 m) = ((S m) = (term1 m)).
Proof. exact (eq_refl (term0 m)). Qed.