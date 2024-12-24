Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1071681_term_abbrevs.
Lemma lem1071681 {A : Type'} : (@cons A) = (term0 A).
Proof. exact (@CONS_def A). Qed.
