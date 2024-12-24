Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416541_term_abbrevs.
Require Import thm2416538_spec.
Lemma lem2416541 (lx : int) (ly : int) (rx : int) (ry : int) : (term0 lx ly rx ry) = (term1 lx ly rx ry).
Proof. exact (proj1 (@lem2416538 ly rx lx ry (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
