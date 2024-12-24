Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516558_term_abbrevs.
Require Import thm124233_spec.
Lemma lem516557 : term0.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem516558 (n : nat) : term1 n.
Proof. exact (@lem516557 n). Qed.
