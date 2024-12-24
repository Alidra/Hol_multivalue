Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184692_term_abbrevs.
Require Import thm3183344_spec.
Require Import thm3183432_spec.
Require Import thm3183558_spec.
Lemma lem3184691 {_83123 : Type'} (x : _83123) : (@SETSPEC _83123 x) = (term0 _83123 x).
Proof. exact (EQ_MP (@lem3183432 _83123 x) (@lem3183558 _83123 x)). Qed.
Lemma lem3184692 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term1 _83123 P x) = (term2 _83123 P x).
Proof. exact (MK_COMB (@lem3183344 _83123 P) (@lem3184691 _83123 x)). Qed.
