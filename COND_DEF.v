Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_DEF_term_abbrevs.
Lemma lem12296 {A : Type'} : (@COND A) = (term0 A).
Proof. exact (@COND_def A). Qed.
