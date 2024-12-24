Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416561_term_abbrevs.
Require Import thm2416558_spec.
Lemma lem2416561 (a : int) (c : int) (b : int) : (term0 a b c) = (term0 a c b).
Proof. exact (proj1 (@lem2416558 b a c (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
