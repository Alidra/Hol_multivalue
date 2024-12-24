Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982722_spec.
Lemma lem1982725 (b : real) (a : real) : (real_mul a b) = (real_mul b a).
Proof. exact (proj1 (@lem1982722 (@el real) (@el real) (@el real) (@el real) b a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
