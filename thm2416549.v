Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416546_spec.
Lemma lem2416549 (rx : int) (lx : int) : (int_mul lx rx) = (int_mul rx lx).
Proof. exact (proj1 (@lem2416546 rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
