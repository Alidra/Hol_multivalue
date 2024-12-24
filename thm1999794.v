Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1999794_term_abbrevs.
Require Import thm1386578_spec.
Lemma lem1999794 (x : real) (y : real) : term0 x y.
Proof. exact (@lem1386578 ((real_lt x y) = (term1 x y))). Qed.
