Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516896_term_abbrevs.
Require Import thm516884_spec.
Lemma lem516895 : term0.
Proof. exact (proj1 (@lem516884)). Qed.
Lemma lem516896 (m : nat) : term1 m.
Proof. exact (@lem516895 m). Qed.
