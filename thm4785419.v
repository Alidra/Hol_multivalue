Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4785419_term_abbrevs.
Lemma lem4785419 {A : Type'} : (@set_of_list A) = (term0 A).
Proof. exact (@set_of_list_def A). Qed.
