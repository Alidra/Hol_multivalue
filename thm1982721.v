Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982721_term_abbrevs.
Require Import thm1982718_spec.
Lemma lem1982721 (a : real) : (term0 a) = a.
Proof. exact (proj1 (@lem1982718 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
