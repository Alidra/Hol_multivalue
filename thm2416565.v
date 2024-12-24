Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416565_term_abbrevs.
Require Import thm2416562_spec.
Lemma lem2416565 (a : int) (c : int) (d : int) : (term0 a c d) = (term1 a c d).
Proof. exact (proj1 (@lem2416562 a c d (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
