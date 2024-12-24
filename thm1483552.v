Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483552_term_abbrevs.
Require Import thm1483550_spec.
Lemma lem1483552 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483550 x y)). Qed.
