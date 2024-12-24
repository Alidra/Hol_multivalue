Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import _MATCH_term_abbrevs.
Lemma lem44160 {_4656 _4660 : Type'} : (@_MATCH _4656 _4660) = (term0 _4656 _4660).
Proof. exact (@_MATCH_def _4656 _4660). Qed.
