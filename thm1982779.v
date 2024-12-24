Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982779_term_abbrevs.
Require Import thm1982776_spec.
Lemma lem1982779 (x : real) : (term0 x) = x.
Proof. exact (proj1 (@lem1982776 (@el real) (@el real) x (@el nat))). Qed.
