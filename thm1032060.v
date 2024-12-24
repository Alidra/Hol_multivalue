Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032060_term_abbrevs.
Require Import thm1032057_spec.
Lemma lem1032060 (a : nat) : (term0 a) = a.
Proof. exact (proj1 (@lem1032057 (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) a (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
