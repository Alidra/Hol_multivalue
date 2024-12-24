Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637144_term_abbrevs.
Require Import thm7_spec.
Lemma lem7637144 (n : nat) : (term0 n) = ((term0 n) = True).
Proof. exact (@lem7 (term0 n)). Qed.
