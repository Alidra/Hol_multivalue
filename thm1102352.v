Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102352_term_abbrevs.
Lemma lem1102352 {_25350 _25351 : Type'} : (@ITLIST _25350 _25351) = (term0 _25350 _25351).
Proof. exact (@ITLIST_def _25350 _25351). Qed.
