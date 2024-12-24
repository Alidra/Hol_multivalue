Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841544_term_abbrevs.
Require Import thm2841543_spec.
Lemma lem2841544 (x : int) (y : int) : term0 x y.
Proof. exact (proj2 (@lem2841543 x y)). Qed.
