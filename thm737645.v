Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm737645_term_abbrevs.
Require Import thm737643_spec.
Lemma lem737644 : term0.
Proof. exact (proj2 (@lem737643)). Qed.
Lemma lem737645 (n : nat) : term1 n.
Proof. exact (@lem737644 n). Qed.
