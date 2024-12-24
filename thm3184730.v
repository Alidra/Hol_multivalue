Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184730_term_abbrevs.
Require Import thm3184719_spec.
Require Import thm3184729_spec.
Lemma lem3184730 {_83123 _83152 _83169 : Type'} : term0 _83123 _83152 _83169.
Proof. exact (conj (@lem3184729 _83123) (@lem3184719 _83152 _83169)). Qed.
