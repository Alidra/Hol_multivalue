Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982745_term_abbrevs.
Require Import thm1982742_spec.
Lemma lem1982745 (lx : real) (ly : real) (rx : real) : (term0 lx ly rx) = (term1 lx ly rx).
Proof. exact (proj1 (@lem1982742 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
