Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841543_term_abbrevs.
Require Import thm2841542_spec.
Lemma lem2841543 (x : int) (y : int) : term0 x y.
Proof. exact (proj2 (@lem2841542 x y)). Qed.
