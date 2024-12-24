Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980011_term_abbrevs.
Require Import thm1980010_spec.
Lemma lem1980011 (x : nat) (y : nat) : term0 x y.
Proof. exact (proj2 (@lem1980010 x y)). Qed.
