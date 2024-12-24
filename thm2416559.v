Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416559_term_abbrevs.
Require Import thm2416556_spec.
Lemma lem2416559 (c : int) (a : int) (d : int) : (term0 a c d) = (term0 c a d).
Proof. exact (proj1 (@lem2416556 (@el int) a c d (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
