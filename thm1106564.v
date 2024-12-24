Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106562_spec.
Require Import thm1106563_spec.
Lemma lem1106564 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
