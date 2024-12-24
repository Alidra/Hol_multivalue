Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108877_term_abbrevs.
Lemma lem1108877 {_25719 _25727 : Type'} : (@ZIP _25719 _25727) = (term0 _25719 _25727).
Proof. exact (@ZIP_def _25719 _25727). Qed.
