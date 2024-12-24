Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988289_term_abbrevs.
Require Import thm1988286_spec.
Lemma lem1988289 (x : real) (y : real) : (real_gt x y) = (term0 x y).
Proof. exact (proj1 (@lem1988286 x y)). Qed.
