Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416521_term_abbrevs.
Require Import thm2416518_spec.
Lemma lem2416521 (m : int) : (term0 m) = term1.
Proof. exact (proj1 (@lem2416518 m (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
