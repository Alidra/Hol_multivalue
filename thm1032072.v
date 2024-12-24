Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032072_term_abbrevs.
Require Import thm1032069_spec.
Lemma lem1032072 (a : nat) : (term0 a) = a.
Proof. exact (proj1 (@lem1032069 (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) a (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
