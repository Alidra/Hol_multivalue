Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103131_term_abbrevs.
Lemma lem1103131 {_25376 : Type'} : (@List.In _25376) = (term0 _25376).
Proof. exact (@MEM_def _25376). Qed.
