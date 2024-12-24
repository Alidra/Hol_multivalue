Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416571_term_abbrevs.
Require Import thm2416568_spec.
Lemma lem2416571 (x : int) (q : nat) : (term0 q x) = (term1 x q).
Proof. exact (proj1 (@lem2416568 (@el nat) (@el int) (@el int) x q)). Qed.
