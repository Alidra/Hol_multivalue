Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982727_term_abbrevs.
Require Import thm1982724_spec.
Lemma lem1982727 (a : real) (b : real) (c : real) : (term0 a b c) = (term1 a b c).
Proof. exact (proj1 (@lem1982724 (@el real) (@el real) (@el real) (@el real) b a c (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
