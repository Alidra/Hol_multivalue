Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm71261_term_abbrevs.
Lemma lem71261 (r : ind) : (NUM_REP r) = ((term0 r) = r).
Proof. exact (@axiom_8 r). Qed.
