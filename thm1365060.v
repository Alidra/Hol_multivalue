Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm1365059_spec.
Lemma lem1365060 : (False /\ True) = False.
Proof. exact (EQ_MP (@lem1365059) (@lem0)). Qed.
