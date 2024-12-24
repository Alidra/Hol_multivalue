Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405757_term_abbrevs.
Require Import thm2405756_spec.
Lemma lem2405757 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj2 (@lem2405756 m n)). Qed.
