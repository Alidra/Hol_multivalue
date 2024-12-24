Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483444_term_abbrevs.
Require Import thm1483441_spec.
Lemma lem1483444 (m : real) : (real_add m m) = (term0 m).
Proof. exact (proj1 (@lem1483441 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
