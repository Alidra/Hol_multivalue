Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184696_term_abbrevs.
Require Import thm3183195_spec.
Require Import thm3184692_spec.
Lemma lem3184696 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term0 _83123 P x) = (term1 _83123 P x).
Proof. exact (EQ_MP (@lem3183195 _83123 P x) (@lem3184692 _83123 P x)). Qed.
