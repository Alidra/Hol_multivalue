Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100774_term_abbrevs.
Lemma lem1100774 {_25307 : Type'} : (@List.Forall _25307) = (term0 _25307).
Proof. exact (@ALL_def _25307). Qed.
