Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538294_term_abbrevs.
Require Import thm538261_spec.
Lemma lem538293 : term0.
Proof. exact (proj1 (@lem538261)). Qed.
Lemma lem538294 (n : nat) : term1 n.
Proof. exact (@lem538293 n). Qed.
