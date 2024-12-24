Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184741_term_abbrevs.
Require Import thm3184730_spec.
Require Import thm3184740_spec.
Lemma lem3184741 {_83095 _83123 _83152 _83169 : Type'} : term0 _83095 _83123 _83152 _83169.
Proof. exact (conj (@lem3184740 _83095) (@lem3184730 _83123 _83152 _83169)). Qed.
