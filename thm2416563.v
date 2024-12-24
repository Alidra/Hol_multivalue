Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416560_spec.
Lemma lem2416563 (c : int) (a : int) : (int_add a c) = (int_add c a).
Proof. exact (proj1 (@lem2416560 a c (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
