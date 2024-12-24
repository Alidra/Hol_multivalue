Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111401_term_abbrevs.
Lemma lem1111401 {A : Type'} : (@list_of_seq A) = (term0 A).
Proof. exact (@list_of_seq_def A). Qed.
