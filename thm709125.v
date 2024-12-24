Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm709125_term_abbrevs.
Require Import thm709050_spec.
Require Import thm709051_spec.
Lemma lem709124 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem709051 n) (@lem709050 n)). Qed.
Lemma lem709125 : term1 = term2.
Proof. exact (@lem709124 (BIT1 0)). Qed.
