Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SELECT_AX_term_abbrevs.
Lemma lem9221 {A : Type'} : term0 A.
Proof. exact (@axiom_1 A). Qed.
