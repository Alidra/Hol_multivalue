Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Lemma lem1101589 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
