Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416511_term_abbrevs.
Require Import thm2416509_spec.
Lemma lem2416511 (x : int) : (term0 x) = x.
Proof. exact (proj1 (@lem2416509 (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) x (@el nat))). Qed.
