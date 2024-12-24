Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416513_term_abbrevs.
Require Import thm2416510_spec.
Lemma lem2416513 (a : int) (b : int) (m : int) : (term0 a b m) = (term1 a b m).
Proof. exact (proj1 (@lem2416510 m (@el int) (@el int) (@el int) (@el int) b a (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
