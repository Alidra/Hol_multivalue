Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416524_spec.
Lemma lem2416527 (b : int) (a : int) : (int_mul a b) = (int_mul b a).
Proof. exact (proj1 (@lem2416524 (@el int) (@el int) (@el int) (@el int) b a (@el int) (@el int) (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
