Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Lemma lem3322165 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
