Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import I_DEF_term_abbrevs.
Lemma lem15398 {A : Type'} : (@I A) = (term0 A).
Proof. exact (@I_def A). Qed.
