Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm996238_term_abbrevs.
Require Import thm996236_spec.
Lemma lem996238 (n : nat) : (term0 n) = n.
Proof. exact (proj1 (@lem996236 n (@el nat))). Qed.
