Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416553_term_abbrevs.
Require Import thm2416550_spec.
Lemma lem2416553 (rx : int) (lx : int) (ry : int) : (term0 lx rx ry) = (term0 rx lx ry).
Proof. exact (proj1 (@lem2416550 rx lx ry (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
