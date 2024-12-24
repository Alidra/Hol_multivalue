Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm523724_term_abbrevs.
Require Import thm523716_spec.
Lemma lem523718 : term0.
Proof. exact (proj2 (@lem523716)). Qed.
Lemma lem523723 : term1.
Proof. exact (proj1 (@lem523718)). Qed.
Lemma lem523724 (n : nat) : term2 n.
Proof. exact (@lem523723 n). Qed.
