Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032094_term_abbrevs.
Require Import thm1032091_spec.
Lemma lem1032094 (c : nat) (a : nat) (d : nat) : (term0 a c d) = (term0 c a d).
Proof. exact (proj1 (@lem1032091 (@el nat) a c d (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
