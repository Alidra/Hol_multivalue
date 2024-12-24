Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416523_term_abbrevs.
Require Import thm2416520_spec.
Lemma lem2416523 (a : int) : (term0 a) = a.
Proof. exact (proj1 (@lem2416520 (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
