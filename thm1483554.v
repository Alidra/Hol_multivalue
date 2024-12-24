Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483554_term_abbrevs.
Require Import thm1483552_spec.
Lemma lem1483554 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (proj2 (@lem1483552 x y)). Qed.
