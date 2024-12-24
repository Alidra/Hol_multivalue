Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_INTERS_INTERS_term_abbrevs.
Require Import thm4380553_spec.
Require Import thm4380556_spec.
Lemma lem4380560 {_104907 _104908 : Type'} : term0 _104907 _104908.
Proof. exact (EQ_MP (@lem4380556 _104907 _104908) (@lem4380553 _104907 _104908)). Qed.
