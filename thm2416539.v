Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416539_term_abbrevs.
Require Import thm2416536_spec.
Lemma lem2416539 (lx : int) (rx : int) (ly : int) (ry : int) : (term0 lx ly rx ry) = (term0 lx rx ly ry).
Proof. exact (proj1 (@lem2416536 ly rx lx ry (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
