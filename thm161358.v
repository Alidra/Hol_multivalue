Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161358_term_abbrevs.
Require Import thm161352_spec.
Lemma lem161358 (m : nat) : term0 m.
Proof. exact (fun n : nat => @lem161352 n m). Qed.
