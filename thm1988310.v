Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988310_term_abbrevs.
Require Import thm1988308_spec.
Lemma lem1988310 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1988308 x y)). Qed.