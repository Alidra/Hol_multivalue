Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3354637_spec.
Require Import thm3354697_spec.
Lemma lem3354698 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
