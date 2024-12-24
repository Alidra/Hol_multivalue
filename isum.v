Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6914180 {_126338 : Type'} : (@isum _126338) = (@iterate int _126338 int_add).
Proof. exact (@isum_def _126338). Qed.
