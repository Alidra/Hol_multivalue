Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm3192217_spec.
Lemma lem3192218 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term0 A s x).
Proof. exact (EQ_MP (@lem3192217 A s x) (@lem0)). Qed.
