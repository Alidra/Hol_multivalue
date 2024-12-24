Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982717_term_abbrevs.
Require Import thm1982714_spec.
Lemma lem1982717 (m : real) : (real_add m m) = (term0 m).
Proof. exact (proj1 (@lem1982714 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
