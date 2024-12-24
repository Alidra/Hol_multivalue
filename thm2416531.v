Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416531_term_abbrevs.
Require Import thm2416528_spec.
Lemma lem2416531 (a : int) : (term0 a) = term1.
Proof. exact (proj1 (@lem2416528 (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
