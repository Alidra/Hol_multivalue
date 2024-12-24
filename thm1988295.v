Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988295_term_abbrevs.
Require Import thm1988292_spec.
Lemma lem1988295 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (proj1 (@lem1988292 x y)). Qed.
