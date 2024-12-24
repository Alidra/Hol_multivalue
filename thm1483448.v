Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483448_term_abbrevs.
Require Import thm1483445_spec.
Lemma lem1483448 (a : real) : (term0 a) = a.
Proof. exact (proj1 (@lem1483445 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el nat) (@el real) (@el real) (@el real) (@el nat))). Qed.
