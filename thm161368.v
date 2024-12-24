Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161368_term_abbrevs.
Require Import thm161353_spec.
Lemma lem161368 (m : nat) : term0 m.
Proof. exact (fun n : nat => @lem161353 n m). Qed.
