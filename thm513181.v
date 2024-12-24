Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513181_term_abbrevs.
Require Import thm513125_spec.
Lemma lem513180 : term0.
Proof. exact (proj1 (@lem513125)). Qed.
Lemma lem513181 (n : nat) : term1 n.
Proof. exact (@lem513180 n). Qed.
