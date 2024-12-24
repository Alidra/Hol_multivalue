Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm804_spec.
Require Import thm805_spec.
Lemma lem806 (p : Prop) : (p \/ p) = p.
Proof. exact (EQ_MP (@lem805 p) (@lem804 p)). Qed.
