Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318497_term_abbrevs.
Require Import thm2318496_spec.
Lemma lem2318497 (x : int) (y : int) : term0 x y.
Proof. exact (proj2 (@lem2318496 x y)). Qed.
