Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416519_term_abbrevs.
Require Import thm2416516_spec.
Lemma lem2416519 (m : int) : (int_add m m) = (term0 m).
Proof. exact (proj1 (@lem2416516 m (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
