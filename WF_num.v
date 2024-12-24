Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm365139_spec.
Lemma lem365140 : @WF nat Peano.lt.
Proof. exact (EQ_MP (@lem365139) (@lem0)). Qed.
