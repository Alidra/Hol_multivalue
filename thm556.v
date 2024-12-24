Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm554_spec.
Require Import thm555_spec.
Lemma lem556 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
