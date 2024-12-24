Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm523728_term_abbrevs.
Require Import thm523717_spec.
Lemma lem523728 (n : nat) : term0 n.
Proof. exact (@lem523717 n). Qed.
