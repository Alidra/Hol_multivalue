Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm626_spec.
Require Import thm627_spec.
Lemma lem628 (p : Prop) : (p /\ p) = p.
Proof. exact (EQ_MP (@lem627 p) (@lem626 p)). Qed.