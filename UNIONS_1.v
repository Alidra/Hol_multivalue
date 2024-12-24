Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_1_term_abbrevs.
Require Import thm3322190_spec.
Require Import thm3322871_spec.
Lemma lem3322872 {_86807 : Type'} (s : _86807 -> Prop) : (term0 _86807 s) = s.
Proof. exact (EQ_MP (@lem3322190 _86807 s) (@lem3322871 _86807 s)). Qed.
