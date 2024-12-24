Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416545_term_abbrevs.
Require Import thm2416542_spec.
Lemma lem2416545 (lx : int) (rx : int) (ly : int) : (term0 lx ly rx) = (term0 lx rx ly).
Proof. exact (proj1 (@lem2416542 ly rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
