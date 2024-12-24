Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1068987_term_abbrevs.
Lemma lem1068987 {A B : Type'} : (@OUTR A B) = (term0 A B).
Proof. exact (@OUTR_def A B). Qed.
