Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1482708_term_abbrevs.
Require Import thm1482707_spec.
Lemma lem1482708 (x : real) (a : real) (b : real) (y : real) (c : real) (r : real) : term0 x a b y c r.
Proof. exact (proj2 (@lem1482707 x a b y c r)). Qed.