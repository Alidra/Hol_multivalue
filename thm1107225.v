Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1107225_term_abbrevs.
Lemma lem1107225 {_25617 _25623 : Type'} : (@ASSOC _25617 _25623) = (term0 _25617 _25623).
Proof. exact (@ASSOC_def _25617 _25623). Qed.
