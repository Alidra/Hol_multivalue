Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm10184_spec.
Lemma lem10185 : (~ False) = True.
Proof. exact (EQ_MP (@lem10184) (@lem0)). Qed.
