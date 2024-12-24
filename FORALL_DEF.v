Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_DEF_term_abbrevs.
Lemma lem52 {A : Type'} : (@all A) = (term0 A).
Proof. exact (@all_def A). Qed.
