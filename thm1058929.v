Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZRECSPACE_RULES_spec.
Lemma lem1058929 {A : Type'} : @ZRECSPACE A (@ZBOT A).
Proof. exact (proj1 (@lem1058926 A)). Qed.
