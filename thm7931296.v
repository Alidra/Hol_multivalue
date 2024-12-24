Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931295_spec.
Lemma lem7931296 {A : Type'} : (@_103802 A) = (@mktybit1 A).
Proof. exact (SYM (@lem7931295 A)). Qed.
