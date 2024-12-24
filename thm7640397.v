Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7_spec.
Lemma lem7640397 {M N : Type'} : (@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) = ((@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) = True).
Proof. exact (@lem7 (@FINITE (finite_sum M N) (@UNIV (finite_sum M N)))). Qed.
