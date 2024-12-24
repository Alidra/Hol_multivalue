Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032066_term_abbrevs.
Require Import thm1032063_spec.
Lemma lem1032066 (a : nat) : (term0 a) = (NUMERAL 0).
Proof. exact (proj1 (@lem1032063 (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) a (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
