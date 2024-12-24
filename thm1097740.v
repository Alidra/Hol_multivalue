Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1097740_term_abbrevs.
Lemma lem1097740 {A B : Type'} : (@List.map A B) = (term0 A B).
Proof. exact (@MAP_def A B). Qed.
