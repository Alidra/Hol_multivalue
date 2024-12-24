Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101527_term_abbrevs.
Lemma lem1101527 {_25328 : Type'} : (@EX _25328) = (term0 _25328).
Proof. exact (@EX_def _25328). Qed.
