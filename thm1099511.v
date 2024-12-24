Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099511_term_abbrevs.
Require Import thm1099508_spec.
Lemma lem1099510 {_25272 : Type'} : term0 _25272.
Proof. exact (proj1 (@lem1099508 _25272)). Qed.
Lemma lem1099511 {_25272 : Type'} (x : _25272) : term1 _25272 x.
Proof. exact (@lem1099510 _25272 x). Qed.
