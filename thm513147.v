Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513147_term_abbrevs.
Require Import thm82_spec.
Lemma lem513147 (n : nat) : term0 n.
Proof. exact (@lem82 ((S n) = 0)). Qed.