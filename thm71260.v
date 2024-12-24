Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm71260_term_abbrevs.
Lemma lem71260 (a : nat) : (term0 a) = a.
Proof. exact (@axiom_7 a). Qed.
