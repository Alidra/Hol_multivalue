Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416543_term_abbrevs.
Require Import thm2416540_spec.
Lemma lem2416543 (rx : int) (lx : int) (ly : int) (ry : int) : (term0 lx ly rx ry) = (term1 rx lx ly ry).
Proof. exact (proj1 (@lem2416540 ly rx lx ry (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
