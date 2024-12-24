Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483449_spec.
Lemma lem1483452 (b : real) (a : real) : (real_mul a b) = (real_mul b a).
Proof. exact (proj1 (@lem1483449 (@el real) (@el real) (@el real) (@el real) b a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
