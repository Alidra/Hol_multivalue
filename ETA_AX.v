Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ETA_AX_term_abbrevs.
Lemma lem9121 {A B : Type'} : term0 A B.
Proof. exact (@axiom_0 A B). Qed.
