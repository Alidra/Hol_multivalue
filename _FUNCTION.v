Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import _FUNCTION_term_abbrevs.
Lemma lem44161 {_4678 _4682 : Type'} : (@_FUNCTION _4678 _4682) = (term0 _4678 _4682).
Proof. exact (@_FUNCTION_def _4678 _4682). Qed.
