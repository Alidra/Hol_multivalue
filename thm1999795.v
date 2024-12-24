Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1999795_term_abbrevs.
Require Import thm1999793_spec.
Require Import thm1999794_spec.
Lemma lem1999795 (x : real) (y : real) : (real_lt x y) = (term0 x y).
Proof. exact (@lem1999794 x y (@lem1999793 x y)). Qed.
