Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100049_term_abbrevs.
Lemma lem1100049 {_25287 : Type'} : (@NULL _25287) = (term0 _25287).
Proof. exact (@NULL_def _25287). Qed.
