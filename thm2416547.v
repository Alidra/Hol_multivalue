Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416547_term_abbrevs.
Require Import thm2416544_spec.
Lemma lem2416547 (lx : int) (ly : int) (rx : int) : (term0 lx ly rx) = (term1 lx ly rx).
Proof. exact (proj1 (@lem2416544 ly rx lx (@el int) (@el int) (@el int) (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
