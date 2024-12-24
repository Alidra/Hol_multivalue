Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3790998_term_abbrevs.
Require Import thm3790997_spec.
Lemma lem3790998 {A B : Type'} : term0 A B.
Proof. exact (proj2 (@lem3790997 A B)). Qed.
