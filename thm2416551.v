Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416551_term_abbrevs.
Require Import thm2416548_spec.
Lemma lem2416551 (lx : int) (rx : int) (ry : int) : (term0 lx rx ry) = (term1 lx rx ry).
Proof. exact (proj1 (@lem2416548 rx lx ry (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
