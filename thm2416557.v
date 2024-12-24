Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416557_term_abbrevs.
Require Import thm2416554_spec.
Lemma lem2416557 (a : int) (b : int) (c : int) : (term0 a b c) = (term1 a b c).
Proof. exact (proj1 (@lem2416554 b a c (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
