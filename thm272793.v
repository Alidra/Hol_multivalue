Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm272793_term_abbrevs.
Require Import ADD_AC_spec.
Lemma lem272793 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
