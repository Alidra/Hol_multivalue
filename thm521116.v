Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm521116_term_abbrevs.
Require Import thm82_spec.
Lemma lem521116 (n : nat) (m : nat) : term0 n m.
Proof. exact (@lem82 (term1 n m)). Qed.
