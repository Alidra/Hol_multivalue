Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516897_term_abbrevs.
Lemma lem516897 (m : nat) : (term0 m) = ((Peano.le m 0) = (m = 0)).
Proof. exact (eq_refl (term0 m)). Qed.
