Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416515_term_abbrevs.
Require Import thm2416512_spec.
Lemma lem2416515 (a : int) (m : int) : (term0 a m) = (term1 a m).
Proof. exact (proj1 (@lem2416512 m (@el int) (@el int) (@el int) (@el int) (@el int) a (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
